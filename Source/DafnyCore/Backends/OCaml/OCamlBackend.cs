using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class OCamlBackend : ExecutableBackend {

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new OCamlCodeGenerator(Options, Reporter);
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

  // The runtime module (DafnyRuntime.ml) lives next to the dafny executable, alongside any
  // other files that were emitted into the output directory (when --include-runtime is set).
  private string FindRuntimeSource(string targetFilename) {
    var siblingCopy = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(targetFilename))!, "DafnyRuntime.ml");
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
    if (otherFileNames.Count > 0) {
      await outputWriter.Status("Unrecognized argument to OCaml compiler: extra files are not supported.");
      return (false, null);
    }

    var runtimeSource = FindRuntimeSource(targetFilename);
    var outputDir = Path.GetDirectoryName(Path.GetFullPath(targetFilename))!;
    var psi = PrepareProcessStartInfo("ocamlfind", new List<string> {
      "ocamlopt",
      "-package", "zarith",
      "-linkpkg",
      "-w", "-a", // the generated code deliberately doesn't try to satisfy every OCaml warning
      "-I", outputDir,
      runtimeSource,
      targetFilename,
      "-o", ComputeExeName(targetFilename)
    });
    await using var statusWriter = outputWriter.StatusWriter();
    return (0 == await RunProcess(psi, statusWriter, statusWriter, "Error while compiling OCaml files."), null);
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

This back-end favors simplicity over completeness (see Docs/Compilation/OCaml.md).
Notable limitations include a lack of support for traits, co-inductive types, and iterators.";
    return cmd;
  }

  public override void CleanSourceDirectory(string sourceDirectory) {
    foreach (var ext in new[] { "*.cmi", "*.cmx", "*.o" }) {
      foreach (var f in Directory.GetFiles(sourceDirectory, ext)) {
        File.Delete(f);
      }
    }
  }

  public OCamlBackend(DafnyOptions options) : base(options) {
  }
}
