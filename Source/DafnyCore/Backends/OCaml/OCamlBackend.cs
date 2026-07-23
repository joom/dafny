using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class OCamlBackend : ExecutableBackend {

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new OCamlCodeGenerator(Options, Reporter);
  }

  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    base.Compile(dafnyProgram, dafnyProgramName, output);
    ((OCamlCodeGenerator)codeGenerator).FinishCompilation();
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".ml" };

  public override string TargetName => "OCaml";
  public override bool IsStable => false;
  public override string TargetExtension => "ml";

  public override bool SupportsInMemoryCompilation => false;

  public override bool TextualTargetIsExecutable => false;

  public override IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "number", "ulong", "long" };

  private string ComputeExeName(string targetFilename) {
    return Path.ChangeExtension(Path.GetFullPath(targetFilename), "exe");
  }

  // The runtime module (dafnyRuntime.ml) lives next to the generated source, alongside any
  // other files that were emitted into the output directory (when --include-runtime is set).
  private string FindRuntimeSource(string targetFilename) {
    var siblingCopy = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(targetFilename))!, "dafnyRuntime.ml");
    if (File.Exists(siblingCopy)) {
      return siblingCopy;
    }
    var assemblyLocation = System.Reflection.Assembly.GetExecutingAssembly().Location;
    Contract.Assert(assemblyLocation != null);
    var codebase = Path.GetDirectoryName(assemblyLocation);
    Contract.Assert(codebase != null);
    return Path.Combine(codebase, "DafnyRuntimeOCaml", "dafnyRuntime.ml");
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, IDafnyOutputWriter outputWriter) {
    foreach (var otherFileName in otherFileNames) {
      if (!string.Equals(Path.GetExtension(otherFileName), ".ml", StringComparison.OrdinalIgnoreCase)) {
        await outputWriter.Status($"Unrecognized file as extra input for OCaml compilation: {otherFileName}");
        return (false, null);
      }
    }

    var runtimeSource = FindRuntimeSource(targetFilename);
    if (!File.Exists(runtimeSource)) {
      await outputWriter.Status($"Could not find the OCaml runtime source at {runtimeSource}.");
      return (false, null);
    }

    var targetPath = Path.GetFullPath(targetFilename);
    var outputDir = Path.GetDirectoryName(targetPath)!;
    var buildDirectory = Path.Combine(Path.GetTempPath(), "dafny-ocaml-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(buildDirectory);

    try {
      // ocamlopt writes .cmi/.cmx/.o files beside its inputs. Copy every input into a private
      // directory so compilation never modifies either Dafny's installation or the user's
      // source/output directory. Keeping each basename also preserves the OCaml module name.
      var inputs = new List<string>();
      var occupiedBasenames = new HashSet<string>(StringComparer.OrdinalIgnoreCase);

      async Task<bool> CopyInput(string source, string destinationBasename = null) {
        var basename = destinationBasename ?? Path.GetFileName(source);
        if (!occupiedBasenames.Add(basename)) {
          await outputWriter.Status(
            $"OCaml compilation has more than one input named {basename} ({source}).");
          return false;
        }
        try {
          File.Copy(Path.GetFullPath(source), Path.Combine(buildDirectory, basename));
        } catch (Exception e) when (e is IOException or UnauthorizedAccessException or NotSupportedException) {
          await outputWriter.Status($"Could not stage {source} for OCaml compilation: {e.Message}");
          return false;
        }
        inputs.Add(basename);
        return true;
      }

      if (!await CopyInput(runtimeSource)) {
        return (false, null);
      }
      foreach (var otherFileName in otherFileNames) {
        if (!File.Exists(otherFileName)) {
          await outputWriter.Status($"OCaml extra input does not exist: {otherFileName}");
          return (false, null);
        }
        if (!await CopyInput(otherFileName)) {
          return (false, null);
        }
      }

      // Every non-default Dafny module was written out as its own file, alongside the main file
      // (see OCamlCodeGenerator.CreateModule); GeneratedModuleFiles lists them in dependency
      // order. The main file (which may depend on any of them) always goes last.
      foreach (var generatedModule in ((OCamlCodeGenerator)codeGenerator).GeneratedModuleFiles) {
        var modulePath = Path.Combine(outputDir, generatedModule);
        if (!await CopyInput(modulePath)) {
          return (false, null);
        }
      }
      // The user's Dafny filename need not be a legal OCaml compilation-unit name (for example,
      // it may contain '-'). Nothing imports the main/default module, so stage it under a fixed
      // valid name and avoid warning 24 without changing any generated module references.
      var stagedMainBasename = "dafny_program.ml";
      for (var suffix = 2; occupiedBasenames.Contains(stagedMainBasename); suffix++) {
        stagedMainBasename = $"dafny_program_{suffix}.ml";
      }
      if (!await CopyInput(targetPath, stagedMainBasename)) {
        return (false, null);
      }

      var args = new List<string> {
        "ocamlopt",
        "-package", "zarith",
        "-linkpkg",
        // These arise systematically from generated defensive match arms, exception-based
        // returns, and source-level parameters that Dafny permits callers not to use. Keep all
        // other warnings enabled: in particular, warning 20 catches accidental partial
        // applications/extra arguments in the generated calling convention.
        "-w", "-11-21-26",
        "-I", buildDirectory
      };
      args.AddRange(inputs);
      args.AddRange(new[] { "-o", ComputeExeName(targetFilename) });
      var psi = PrepareProcessStartInfo("ocamlfind", args);
      psi.WorkingDirectory = buildDirectory;
      await using var statusWriter = outputWriter.StatusWriter();
      return (0 == await RunProcess(psi, statusWriter, statusWriter,
        "Error while compiling OCaml files."), null);
    } finally {
      try {
        Directory.Delete(buildDirectory, true);
      } catch (IOException) {
        // A failed cleanup must not hide the compiler result.
      } catch (UnauthorizedAccessException) {
        // Likewise on platforms where antivirus/indexing briefly holds a generated file.
      }
    }
  }

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, IDafnyOutputWriter outputWriter) {
    var psi = PrepareProcessStartInfo(ComputeExeName(targetFilename), Options.MainArgs);

    await using var sw = outputWriter.StatusWriter();
    await using var ew = outputWriter.ErrorWriter();
    return 0 == await RunProcess(psi, sw, ew);
  }

  public override Command GetCommand() {
    var cmd = base.GetCommand();
    cmd.Description = $@"Translate Dafny sources to {TargetName} source and build files.

This back-end favors simplicity over completeness (see docs/Compilation/OCaml.md).
Notable limitations include a lack of support for iterators.";
    return cmd;
  }

  public OCamlBackend(DafnyOptions options) : base(options) {
  }
}
