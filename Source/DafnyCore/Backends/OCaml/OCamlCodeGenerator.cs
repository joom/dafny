//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;
using JetBrains.Annotations;

namespace Microsoft.Dafny.Compilers {

  // This backend deliberately favors simplicity over completeness and performance. See
  // docs/Compilation/OCaml.md for the design rationale. In short:
  //   - Every Dafny module gets its own OCaml file/compilation unit (the default module is
  //     folded into the main file, like the Go and Rust backends do). Within a single module,
  //     every class/datatype/etc. is still flattened together (no attempt to use OCaml's module
  //     system to mirror *nested* structure within a Dafny module). Name clashes are avoided by
  //     mangling every top-level name with its enclosing module and class/datatype name, and a
  //     reference to a declaration from a different Dafny module is qualified with that module's
  //     OCaml module name (see ModuleQualifier) — Dafny's import graph is required to be acyclic,
  //     so this always produces a valid (non-circular) OCaml compilation order.
  //   - Within one module's file, type declarations are threaded together into a single
  //     `type ... and ... and ...` block. Top-level values are dependency-sorted and only
  //     genuinely recursive strongly connected components use `let rec ... and ...`; this
  //     preserves OCaml polymorphism while satisfying its "define before use" rule.
  //   - Every local variable and formal parameter is compiled to an OCaml `ref` cell, read with
  //     `!` and written with `:=`. This is not idiomatic OCaml, but it means the compiler doesn't
  //     need to distinguish mutable from immutable bindings, which keeps it simple.
  //   - Classes compile to mutable records; every class reference (nullable `C?` or not — see
  //     InstanceClassAccessor) is a `'a option`, and `null` is `None`. Each object carries a
  //     separate identity token, preserved by trait/object upcasts and used for reference
  //     equality. Every non-static method/function also gets a closure field (wired to the
  //     corresponding top-level function, applied to the record itself), because the framework
  //     compiles every instance call as `receiver.name(args)`, not just field reads.
  //   - `int` (and all bit-vector/native numeric types) is Zarith's arbitrary-precision `Z.t`;
  //     `real` is Zarith's `Q.t`; `char` is a plain `int` Unicode code point.
  //   - `seq` values and one-dimensional array storage use OCaml arrays; Dafny array references
  //     are option-wrapped. `set` is a deduplicated list, `multiset` is an
  //     (element, multiplicity) list, and `map` is an association list. See the OCaml runtime.
  class OCamlCodeGenerator : SinglePassCodeGenerator {

    public OCamlCodeGenerator(DafnyOptions options, ErrorReporter reporter) : base(options, reporter) {
    }

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.Iterators,
      Feature.TypeTests,
      Feature.SubsetTypeTests,
      Feature.SubtypeConstraintsInQuantifiers,
      Feature.MethodSynthesis,
      Feature.BuiltinsInRuntime,
      Feature.RuntimeCoverageReport,
      Feature.StandardLibraries,
      Feature.StandardLibrariesActionsExterns,
      Feature.ExternalClasses,
      Feature.ExternalConstructors,
      Feature.SeparateCompilation,
      Feature.AllUnderscoreExternalModuleNames,
    };

    public override string ModuleSeparator => "__";
    // Everything is flattened (see the class comment), so "member access" for a static
    // function/method is really just the flat-name separator, not a real qualifier.
    protected override string StaticClassAccessor => ModuleSeparator;
    protected override string IsMethodName => "d_is";
    // Instance calls compile as `receiver.name(args)` — the framework writes this as
    // `(<receiver-expr>)<InstanceClassAccessor><name>(<args>)`, with no opportunity to insert an
    // explicit coercion around the receiver first. Since every class reference (nullable or
    // not — see the class comment) is a `'a option`, this needs to unwrap the receiver before
    // reading the closure field named `name` off of it.
    //
    // This can't be done with `receiver |> DafnyRuntime.unwrap |> fun self -> self.name`: unlike
    // `|>` to a plain named function, `fun ... -> ...` has no closing delimiter here (there's
    // nothing after `<name>(<args>)` for us to close it with), so its body silently swallows
    // *every subsequent statement* in the enclosing block as well (`fun`, like `if`/`match`,
    // extends as far right as it can — that's exactly why every other place this backend uses a
    // lambda takes care to close it with a `)`). The custom postfix-*ish* operator `.%()` (see
    // EmitHeader) sidesteps this: `expr.%(())` behaves like ordinary (non-greedy) field access
    // applied to `DafnyRuntime.unwrap expr`.
    protected override string InstanceClassAccessor => ".%(()).";
    protected override bool SupportsProperties => false;
    protected override bool InstanceConstAreStatic() => false;

    // OCaml variants do not have fields or methods. Compile every datatype instance member as
    // a top-level function with an explicit receiver, not only members of ghost/erased variants.
    public override bool NeedsCustomReceiverInDatatype(MemberDecl member) {
      Contract.Requires(!member.IsStatic && member.EnclosingClass is DatatypeDecl);
      return true;
    }

    protected override ConcreteSyntaxTree EmitNullTest(bool testIsNull, ConcreteSyntaxTree wr) {
      wr.Write("(match ");
      var target = wr.Fork();
      wr.Write(testIsNull
        ? " with None -> true | Some _ -> false)"
        : " with None -> false | Some _ -> true)");
      return target;
    }

    protected override ConcreteSyntaxTree EmitCallToIsMethod(
      RedirectingTypeDecl declaration, Type type, ConcreteSyntaxTree wr) {
      // The internal _System module is omitted from normal compilation. `nat` is the one
      // built-in redirecting type whose compilable constraint is invoked by generated _Is
      // bodies, so lower that constraint directly instead of referring to a nonexistent module.
      if (declaration is TopLevelDecl { EnclosingModuleDefinition.Name: "_System", Name: "nat" }) {
        wr.Write("(DafnyRuntime.Int.ge (");
        var argument = wr.Fork();
        wr.Write(", DafnyRuntime.Int.zero))");
        return argument;
      }
      return base.EmitCallToIsMethod(declaration, type, wr);
    }

    // ----- Buffers that everything gets threaded into, one set per OCaml file/Dafny module ----

    // The non-greedy accessor operator (see InstanceClassAccessor) needs to be defined once per
    // file, since each Dafny module becomes its own separate OCaml compilation unit.
    private const string AccessorOperatorDecl =
      "let ( .%() ) (o : 'a option) (_ : unit) : 'a = DafnyRuntime.unwrap o";

    private class ModuleBlocks {
      // `exception` declarations, used to compile `break`/`continue` (see CreateLabeledCode).
      public ConcreteSyntaxTree ExceptionBlock;
      public readonly HashSet<string> DeclaredExceptions = [];

      // All `type` declarations (records for classes, variants for datatypes), joined with `and`.
      public ConcreteSyntaxTree TypeBlock;
      public bool AnyTypeDeclared;

      // Rendered top-level function/method declarations.
      public ConcreteSyntaxTree ValueBlock;
      public readonly List<ValueDecl> Values = [];
      public bool ValuesRendered;
    }

    private class ValueDecl {
      public readonly string Name;
      public readonly string Header;
      public readonly ConcreteSyntaxTree Body = new();

      public ValueDecl(string header) {
        Header = header;
        Name = header.Split([' ', ':', '('], 2)[0];
      }
    }

    // One entry per Dafny module that has been compiled so far (see CreateModule/FinishModule).
    private readonly Dictionary<ModuleDefinition, ModuleBlocks> moduleBlocks = new();
    // The blocks of whichever module is currently being compiled (mirrors enclosingModule).
    private ModuleBlocks currentBlocks;

    private void DeclareExceptionOnce(string name) {
      if (currentBlocks.DeclaredExceptions.Add(name)) {
        currentBlocks.ExceptionBlock.WriteLine("exception {0}", name);
      }
    }

    private ConcreteSyntaxTree NewTypeDecl(string header) {
      var typeBlock = currentBlocks.TypeBlock;
      typeBlock.Write(currentBlocks.AnyTypeDeclared ? "and " : "type ");
      currentBlocks.AnyTypeDeclared = true;
      typeBlock.Write(header);
      var w = typeBlock.Fork(1);
      typeBlock.WriteLine();
      return w;
    }

    // Records a top-level value/function for dependency ordering in FinishCompilation, unless
    // `blocks` is given explicitly (used when a helper conceptually belongs to a *different*
    // module than the one currently being compiled — see DatatypeToStringFunction).
    private ConcreteSyntaxTree NewValueDecl(string header) => NewValueDecl(currentBlocks, header);

    private ConcreteSyntaxTree NewValueDecl(ModuleBlocks blocks, string header) {
      Contract.Assert(!blocks.ValuesRendered);
      var declaration = new ValueDecl(header);
      blocks.Values.Add(declaration);
      return declaration.Body;
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("(* Dafny program {0} compiled into OCaml *)", program.Name);
      if (Options.IncludeRuntime) {
        EmitRuntimeSource("DafnyRuntimeOCaml", wr);
      }
      // See InstanceClassAccessor for why this needs to be a custom (non-greedy) operator rather
      // than a `fun`-based one. This covers the default module, which is folded into this (the
      // main) file; CreateModule repeats this line for every other file it creates.
      wr.WriteLine(AccessorOperatorDecl);
    }

    // Ensures a module's recursive type chain is never empty.
    private void FinishBlocks(ModuleBlocks blocks) {
      if (!blocks.AnyTypeDeclared) {
        blocks.TypeBlock.WriteLine("type __dafny_unused_placeholder__ = unit");
      }
    }

    protected override void FinishModule() {
      FinishBlocks(currentBlocks);
    }

    // Value bodies can be added lazily to an already-compiled module (most notably datatype
    // printers), so they cannot be ordered in FinishModule. OCamlBackend calls this once after
    // the whole Dafny program has been translated but before the syntax trees are rendered.
    public void FinishCompilation() {
      foreach (var allocator in classAllocators) {
        // Allocators are filled only after all class members have been seen. At that point,
        // enclosingModule/currentBlocks normally refer to the last module in the program, but
        // names emitted here must be resolved in the class's own module.
        var savedModule = enclosingModule;
        var savedBlocks = currentBlocks;
        try {
          enclosingModule = allocator.Key.EnclosingModuleDefinition;
          currentBlocks = moduleBlocks[enclosingModule];
          BuildClassInstance(allocator.Key, allocator.Value);
        } finally {
          enclosingModule = savedModule;
          currentBlocks = savedBlocks;
        }
      }
      foreach (var blocks in moduleBlocks.Values) {
        RenderValues(blocks);
      }
    }

    private void RenderValues(ModuleBlocks blocks) {
      Contract.Assert(!blocks.ValuesRendered);
      blocks.ValuesRendered = true;
      if (blocks.Values.Count == 0) {
        blocks.ValueBlock.WriteLine("let __dafny_unused_placeholder__ () = ()");
        return;
      }

      var count = blocks.Values.Count;
      var indicesOfName = new Dictionary<string, List<int>>(count, StringComparer.Ordinal);
      for (var i = 0; i < count; i++) {
        indicesOfName.GetOrCreate(blocks.Values[i].Name, () => []).Add(i);
      }
      var dependencies = Enumerable.Range(0, count).Select(_ => new HashSet<int>()).ToArray();
      for (var i = 0; i < count; i++) {
        foreach (var identifier in ReferencedIdentifiers(blocks.Values[i].Body.ToString())) {
          if (indicesOfName.TryGetValue(identifier, out var referenced)) {
            dependencies[i].UnionWith(referenced);
          }
        }
      }

      // Tarjan's algorithm partitions the dependency graph into exactly the declarations that
      // need to share an OCaml recursive group. The walk is iterative rather than recursive:
      // a dependency chain is as deep as the program's call graph, which is far more than the
      // CLR stack can absorb one frame at a time.
      var nextIndex = 0;
      var indices = Enumerable.Repeat(-1, count).ToArray();
      var lowLinks = new int[count];
      var onStack = new bool[count];
      var stack = new Stack<int>();
      var components = new List<List<int>>();
      var visiting = new Stack<(int Vertex, IEnumerator<int> Dependencies)>();

      void Discover(int vertex) {
        indices[vertex] = lowLinks[vertex] = nextIndex++;
        stack.Push(vertex);
        onStack[vertex] = true;
        visiting.Push((vertex, ((IEnumerable<int>)dependencies[vertex]).GetEnumerator()));
      }

      for (var root = 0; root < count; root++) {
        if (indices[root] != -1) {
          continue;
        }
        Discover(root);
        while (visiting.Count > 0) {
          var (vertex, remainingDependencies) = visiting.Peek();
          if (remainingDependencies.MoveNext()) {
            var dependency = remainingDependencies.Current;
            if (indices[dependency] == -1) {
              Discover(dependency);
            } else if (onStack[dependency]) {
              lowLinks[vertex] = Math.Min(lowLinks[vertex], indices[dependency]);
            }
            continue;
          }
          visiting.Pop();
          if (visiting.Count > 0) {
            var caller = visiting.Peek().Vertex;
            lowLinks[caller] = Math.Min(lowLinks[caller], lowLinks[vertex]);
          }
          if (lowLinks[vertex] != indices[vertex]) {
            continue;
          }
          var component = new List<int>();
          int member;
          do {
            member = stack.Pop();
            onStack[member] = false;
            component.Add(member);
          } while (member != vertex);
          component.Sort();
          components.Add(component);
        }
      }

      var componentOf = new int[count];
      for (var i = 0; i < components.Count; i++) {
        foreach (var member in components[i]) {
          componentOf[member] = i;
        }
      }
      var componentDependencies = components.Select(_ => new HashSet<int>()).ToArray();
      for (var i = 0; i < count; i++) {
        foreach (var dependency in dependencies[i]) {
          if (componentOf[i] != componentOf[dependency]) {
            componentDependencies[componentOf[i]].Add(componentOf[dependency]);
          }
        }
      }

      // Also iterative, for the same reason as the Tarjan walk above: this is a post-order
      // traversal of the (acyclic) condensation, so its depth is that of the call graph.
      var emitted = new bool[components.Count];
      var pending = new Stack<(int Component, bool DependenciesDone)>();

      void EmitComponent(int startComponent) {
        pending.Push((startComponent, false));
        while (pending.Count > 0) {
          var (componentIndex, dependenciesDone) = pending.Pop();
          if (!dependenciesDone) {
            if (emitted[componentIndex]) {
              continue;
            }
            emitted[componentIndex] = true;
            // Queue the write behind every dependency's own write.
            pending.Push((componentIndex, true));
            foreach (var dependency in componentDependencies[componentIndex]) {
              pending.Push((dependency, false));
            }
            continue;
          }
          var component = components[componentIndex];
          var recursive = component.Count > 1 || dependencies[component[0]].Contains(component[0]);
          for (var i = 0; i < component.Count; i++) {
            var declaration = blocks.Values[component[i]];
            blocks.ValueBlock.Write(i == 0 ? recursive ? "let rec " : "let " : "and ");
            blocks.ValueBlock.Write(declaration.Header);
            blocks.ValueBlock.Write(" =");
            blocks.ValueBlock.Append(declaration.Body);
            blocks.ValueBlock.WriteLine();
          }
          blocks.ValueBlock.WriteLine();
        }
      }

      // Stable source order is retained wherever dependency ordering leaves a choice.
      foreach (var componentIndex in Enumerable.Range(0, components.Count)
                 .OrderBy(index => components[index].Min())) {
        EmitComponent(componentIndex);
      }
    }

    // Every identifier a rendered value body could be referring to: each maximal run of
    // identifier characters that isn't preceded by "." (which would make it a record field or a
    // declaration in another OCaml module, not a reference to a same-named value in this
    // compilation unit). Collecting a body's identifiers once and looking each one up — rather
    // than searching every body for every declared name — keeps dependency discovery linear in
    // the size of the generated source instead of quadratic in the number of declarations.
    private static IEnumerable<string> ReferencedIdentifiers(string source) {
      var masked = MaskOCamlStringsAndComments(source);
      for (var i = 0; i < masked.Length; i++) {
        if (!IsIdentifierCharacter(masked[i])) {
          continue;
        }
        var start = i;
        while (i + 1 < masked.Length && IsIdentifierCharacter(masked[i + 1])) {
          i++;
        }
        if (start == 0 || masked[start - 1] != '.') {
          yield return masked.Substring(start, i - start + 1);
        }
      }
    }

    private static bool IsIdentifierCharacter(char c) =>
      c is >= 'A' and <= 'Z' or >= 'a' and <= 'z' or >= '0' and <= '9' or '_' or '\'';

    // Dependency discovery is deliberately performed on rendered OCaml so lazily-generated
    // helpers participate too. Mask literals/comments first: a Dafny string is allowed to
    // contain any generated identifier, and treating that text as a call could spuriously put
    // an ordinary value into an illegal `let rec` group. OCaml comments nest, so handle them
    // with a small scanner rather than a regular expression.
    //
    // This assumes the only literal forms the backend emits are `"..."` strings (see
    // TargetStringLiteral) and `(* ... *)` comments. OCaml character literals ('"') and quoted
    // string literals ({|...|}) would both need handling here before anything starts emitting
    // them, or a stray delimiter inside one would silently corrupt the dependency graph.
    private static string MaskOCamlStringsAndComments(string source) {
      var result = source.ToCharArray();
      var inString = false;
      var commentDepth = 0;
      for (var i = 0; i < result.Length; i++) {
        if (inString) {
          if (result[i] == '\\' && i + 1 < result.Length) {
            result[i++] = ' ';
            result[i] = ' ';
          } else {
            var closesString = result[i] == '"';
            result[i] = ' ';
            inString = !closesString;
          }
          continue;
        }
        if (commentDepth > 0) {
          if (result[i] == '(' && i + 1 < result.Length && result[i + 1] == '*') {
            result[i++] = ' ';
            result[i] = ' ';
            commentDepth++;
          } else if (result[i] == '*' && i + 1 < result.Length && result[i + 1] == ')') {
            result[i++] = ' ';
            result[i] = ' ';
            commentDepth--;
          } else {
            result[i] = ' ';
          }
          continue;
        }
        if (result[i] == '"') {
          result[i] = ' ';
          inString = true;
        } else if (result[i] == '(' && i + 1 < result.Length && result[i + 1] == '*') {
          result[i++] = ' ';
          result[i] = ' ';
          commentDepth = 1;
        }
      }
      return new string(result);
    }

    // The framework's static-Main wrapper (HandleCompilingMainMethod) writes its forwarding call
    // with a hardcoded "." member accessor and a C#-shaped parenthesized argument list, neither
    // of which is OCaml. Suppress it and build the whole call in EmitCallToMain instead, where
    // this backend controls the syntax. Dafny already requires Main to be static, so the only
    // case this opts out of is a Main whose enclosing class is generic — handled below by
    // instantiating the class's type parameters exactly as the wrapper would have.
    protected override bool IssueCreateStaticMain(MethodOrConstructor m) => false;

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      throw new Cce.UnreachableException(); // see IssueCreateStaticMain
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      var enclosingType =
        UserDefinedType.FromTopLevelDeclWithAllBooleanTypeParameters(mainMethod.EnclosingClass);
      var companion = TypeName_Companion(enclosingType, wr, mainMethod.Origin, mainMethod);

      var arguments = new ConcreteSyntaxTree();
      var separator = "";
      var typeArgs = CombineAllTypeArguments(mainMethod, enclosingType.TypeArgs,
        mainMethod.TypeArgs.ConvertAll(_ => (Type)Type.Bool));
      EmitTypeDescriptorsActuals(
        ForTypeDescriptors(typeArgs, mainMethod.EnclosingClass, mainMethod, false),
        mainMethod.Origin, arguments, ref separator);
      // Main may declare a seq<string> parameter to receive the command line. Every backend
      // passes the host's argument vector including the program name in slot 0, so `args[0]`
      // means the same thing here as it does under C#, Go, and Python.
      if (mainMethod.Ins.Any(formal => !formal.IsGhost)) {
        arguments.Write(separator);
        arguments.Write("DafnyRuntime.main_arguments {0}", UnicodeCharEnabled ? "true" : "false");
        separator = ", ";
      }
      if (separator.Length == 0) {
        arguments.Write("()");
      }

      wr.WriteLine("let () =");
      var body = wr.Fork(1);
      body.WriteLine("try {0}{1}{2} ({3})", companion, ModuleSeparator, IdName(mainMethod),
        arguments.ToString());
      body.WriteLine("with DafnyRuntime.Halt msg -> " +
                     "Printf.printf \"%s\\n%!\" (\"[Program halted] \" ^ msg); exit 1");
    }

    // The relative filenames (e.g. "foo.ml") of every non-default module's file, in the order
    // CreateModule created them — i.e. the order the compiler itself processed program.CompileModules
    // in, which (since Dafny requires "import" to name an already-known module) is already a
    // valid dependency order: a module is only ever compiled after the modules it imports. The
    // backend (see OCamlBackend.CompileTargetProgram) uses this to pass all the generated files
    // to ocamlfind in an order it will accept.
    public readonly List<string> GeneratedModuleFiles = new();

    protected override ConcreteSyntaxTree CreateModule(ModuleDefinition module, string moduleName, bool isDefault,
      ModuleDefinition externModule,
      string libraryName /*?*/, Attributes moduleAttributes, ConcreteSyntaxTree wr) {
      ConcreteSyntaxTree fileWr;
      if (isDefault) {
        // Fold the default module into the main file (same as the Go and Rust backends).
        fileWr = wr;
      } else {
        var fileBaseName = ModuleFileBaseName(module);
        GeneratedModuleFiles.Add(fileBaseName + ".ml");
        fileWr = wr.NewFile(fileBaseName + ".ml");
        fileWr.WriteLine("(* Dafny module {0} compiled into OCaml *)", moduleName);
        fileWr.WriteLine(AccessorOperatorDecl);
      }
      var blocks = new ModuleBlocks {
        ExceptionBlock = fileWr.Fork(),
        TypeBlock = fileWr.Fork(),
        ValueBlock = fileWr.Fork()
      };
      moduleBlocks[module] = blocks;
      currentBlocks = blocks;
      return fileWr;
    }

    // Called for every module that was resolved but not translated. Two things reach this hook:
    // the internal _System module, which every backend omits by default (SystemModuleMode.Omit)
    // and which this backend lowers inline instead (see EmitCallToIsMethod); and modules coming
    // from an already-compiled library (--library), which is separate compilation.
    //
    // Nothing is emitted for the latter, yet generated code still refers to the library module's
    // OCaml module — so without this the build fails late, with "Unbound module Dafny_foo" from
    // ocamlopt, instead of the backend feature diagnostic the docs promise.
    protected override void DependOnModule(Program program, ModuleDefinition module,
      ModuleDefinition externModule, string libraryName) {
      if (module.FullName == "_System") {
        return;
      }
      // Report against the program being compiled, not module.Origin: the latter points into the
      // binary .doo the module was read from, so the diagnostic would try to quote a line of it.
      throw new UnsupportedFeatureException(
        program.GetStartOfFirstFileToken(), Feature.SeparateCompilation);
    }

    protected override string GetHelperModuleName() => "DafnyRuntime";

    // ----- Naming -----------------------------------------------------------------------------

    // The base filename (sans ".ml") for a non-default Dafny module's own file, and the OCaml
    // module name that file compiles to (OCaml derives the latter from the former by
    // capitalizing it). The "dafny_" prefix is what makes that capitalization total: every
    // basename starts with a lowercase ASCII letter, so there is no empty/already-uppercase/
    // leading-underscore case to consider.
    private string ModuleFileBaseName(ModuleDefinition m) =>
      "dafny_" + EncodeFilenameIdentifier(m.GetCompileName(Options));

    private string OCamlModuleName(ModuleDefinition m) {
      var baseName = ModuleFileBaseName(m);
      return char.ToUpperInvariant(baseName[0]) + baseName[1..];
    }

    // The OCaml qualifier ("Foo." or "") needed to reference something declared in module `m`
    // from whatever module is currently being compiled. Empty when `m` is the module currently
    // being compiled (no qualifier needed) or the default module (folded into the main file, so
    // it has no OCaml module of its own — see CreateModule).
    private string ModuleQualifier(ModuleDefinition m) {
      if (m == enclosingModule || m.IsDefaultModule) {
        return "";
      }
      return OCamlModuleName(m) + ".";
    }

    // The flattened, globally-unique name of a class/datatype/newtype within its own module's
    // file, never qualified. Safe to use only when constructing a *new*
    // identifier being defined in the same file as `d`, or as one part of a compound identifier
    // that the caller itself qualifies once with ModuleQualifier (see EmitTraitUpcast,
    // EmitCoercionIfNecessary) — everywhere else, use FlatName instead.
    private string RawFlatName(TopLevelDecl d) {
      if (d is NonNullTypeDecl nnd) {
        // `C` (non-null) and `C?` (nullable) share the same underlying record type.
        d = nnd.Class;
      }
      var modName = d.EnclosingModuleDefinition.GetCompileName(Options);
      return EncodeCompoundIdentifier("d_type_", modName, d.GetCompileName(Options));
    }

    // The name of a class/datatype/newtype as referenced from wherever is currently being
    // compiled: RawFlatName, qualified with its module's OCaml module name if that's not the
    // current file.
    private string FlatName(TopLevelDecl d) {
      if (d is NonNullTypeDecl nnd) {
        d = nnd.Class;
      }
      return ModuleQualifier(d.EnclosingModuleDefinition) + RawFlatName(d);
    }

    // ----- Classes ------------------------------------------------------------------------------

    protected class ClassWriter : IClassWriter {
      public readonly string FlatName;
      public readonly OCamlCodeGenerator CodeGenerator;
      public readonly ConcreteSyntaxTree FieldWriter; // fields of the OCaml record, one per line
      public readonly ConcreteSyntaxTree ValueWriter; // where new top-level `let`s get inserted

      public ClassWriter(string flatName, OCamlCodeGenerator codeGenerator, ConcreteSyntaxTree fieldWriter) {
        FlatName = flatName;
        CodeGenerator = codeGenerator;
        FieldWriter = fieldWriter;
        ValueWriter = codeGenerator.currentBlocks.ValueBlock;
      }

      public ConcreteSyntaxTree CreateMethod(MethodOrConstructor m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        var descriptors = CodeGenerator.ForTypeDescriptors(
          typeArgs, m.EnclosingClass, m, lookasideBody);
        return CodeGenerator.CreateSubroutine(FlatName, CodeGenerator.IdName(m), m.Ins, m.Outs,
          m.IsStatic, createBody, false, typeArgs: descriptors, member: m,
          receiverIsOption: lookasideBody, suppressImplicitOutReturn: forBodyInheritance);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(m.Origin, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
        List<Formal> formals, Type resultType, IOrigin tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        var descriptors = CodeGenerator.ForTypeDescriptors(
          typeArgs, member.EnclosingClass, member, lookasideBody);
        return CodeGenerator.CreateSubroutine(FlatName, name, formals, [], isStatic, createBody,
          true, typeArgs: descriptors, member: member, receiverIsOption: lookasideBody);
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IOrigin tok, bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        var typeArguments = member == null
          ? []
          : CodeGenerator.CombineAllTypeArguments(member);
        var descriptors = member == null
          ? []
          : CodeGenerator.ForTypeDescriptors(
            typeArguments, member.EnclosingClass, member, false);
        return CodeGenerator.CreateSubroutine(FlatName, name, [], [], isStatic, createBody, true,
          typeArgs: descriptors, member: member);
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IOrigin tok, bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        setterWriter = createBody
          ? CodeGenerator.CreateSubroutine(FlatName, name + "__set", [], [], false, true, false,
            hasSetterParameter: true,
            typeArgs: CodeGenerator.CombineAllTypeArguments(member), member: member)
          : null;
        return createBody
          ? CodeGenerator.CreateSubroutine(FlatName, name, [], [], false, true, true,
            typeArgs: CodeGenerator.CombineAllTypeArguments(member), member: member)
          : null;
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IOrigin tok, string rhs, Field field) {
        CodeGenerator.DeclareField(FlatName, name, isStatic, type, tok, rhs, field, FieldWriter,
          ValueWriter, enclosingDecl);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new Cce.UnreachableException();
      }

      public ConcreteSyntaxTree ErrorWriter() => ValueWriter;
      public void Finish() { }
    }

    private record InstanceField(string Name, string Initializer);
    private readonly Dictionary<string, List<InstanceField>> instanceFields = new();
    private readonly Dictionary<TopLevelDeclWithMembers, ConcreteSyntaxTree> classAllocators = new();
    private readonly Dictionary<TopLevelDeclWithMembers, string> classPrintNames = new();

    protected void DeclareField(string flatClassName, string name, bool isStatic, Type type, IOrigin tok,
        string rhs, Field field, ConcreteSyntaxTree fieldWriter, ConcreteSyntaxTree wr,
        TopLevelDecl enclosingDecl) {
      var value = rhs ?? DefaultValue(type, wr, tok);
      if (isStatic) {
        var w = NewValueDecl($"{flatClassName}{ModuleSeparator}{name} : {TypeName(type, wr, tok)} ref");
        w.Write("ref ({0})", value);
      } else {
        // Inherited backing fields are referenced directly by framework-generated getter/setter
        // bodies as "_<compile-name>". Own fields use a declaration-qualified label. The second
        // disjunct catches a backing field the framework named itself: it carries
        // InternalFieldPrefix but not the TargetIdPrefix that everything through IdName gets.
        var isBackingField =
          (field != null && field.EnclosingClass != enclosingDecl) ||
          (name.StartsWith(InternalFieldPrefix, StringComparison.Ordinal) &&
           !name.StartsWith(TargetIdPrefix, StringComparison.Ordinal));
        var recordName = isBackingField
          ? name
          : flatClassName + ModuleSeparator + name;
        fieldWriter.WriteLine("mutable {0} : {1};", recordName, TypeName(type, fieldWriter, tok));
        instanceFields.GetOrCreate(flatClassName, () => []).Add(new InstanceField(recordName, value));
      }
    }

    private ConcreteSyntaxTree CreateSubroutine(string flatClassName, string name, List<Formal> ins,
      List<Formal> outs, bool isStatic, bool createBody, bool isFunction,
      bool hasSetterParameter = false, List<TypeArgumentInstantiation> typeArgs = null,
      MemberDecl member = null, bool receiverIsOption = false,
      bool suppressImplicitOutReturn = false) {
      if (!createBody) {
        return null;
      }
      var header = $"{flatClassName}{ModuleSeparator}{name}";
      // The framework emits direct instance calls as f(receiver, arg1, ...), so the receiver
      // must be part of the same OCaml tuple pattern as the explicit arguments. In particular,
      // a zero-argument instance function is `f this`, not the partially-applied `f this ()`.
      var receiver = !isStatic && thisContext is ClassLikeDecl context
        ? $"(this : {RecordTypeName(flatClassName, context.TypeArgs)}" +
          (receiverIsOption ? " option)" : ")")
        : !isStatic ? "this" : null;
      header += " " + SubroutineFormalsPattern(typeArgs, ins, hasSetterParameter, receiver,
        receiverAfterDescriptors: receiverIsOption || thisContext is not ClassLikeDecl);
      var w = NewValueDecl(header);
      var body = w.NewBlock("begin", "end", BlockStyle.Newline, BlockStyle.Newline);
      if (!isStatic && receiverIsOption && thisContext is ClassLikeDecl) {
        body.WriteLine("let this = DafnyRuntime.unwrap this in");
      }
      if (!isStatic && thisContext is ClassLikeDecl receiverContext) {
        var explicitDescriptors = DescriptorArguments(typeArgs)
          .Select(argument => argument.Formal).ToHashSet();
        foreach (var parameter in receiverContext.TypeArgs.Where(NeedsTypeDescriptor)) {
          if (!explicitDescriptors.Contains(parameter)) {
            var descriptor = DescriptorName(parameter);
            body.WriteLine("let {0} = this.{0} in", descriptor);
          }
        }
      }
      var nonGhostIns = ins.Where(f => !f.IsGhost).ToList();
      foreach (var f in nonGhostIns) {
        body.WriteLine("let {0} = ref {0} in", IdName(f));
      }
      // A `return` statement, or a match/if branch of a function body, can produce the
      // subroutine's result from the middle of the statement sequence (not just at the end);
      // see EmitReturn/EmitReturnExpr. Catch that here.
      var tryBlock = body.NewBlock("(try begin", "end with DafnyRuntime.Return __r -> Obj.magic __r)", BlockStyle.Newline, BlockStyle.Newline);
      var beforeReturn = tryBlock.Fork(0);
      if (isFunction) {
        // Functions (and getters) always complete via an explicit EmitReturnExpr-raised
        // DafnyRuntime.Return on every path, so this is unreachable — but it still needs *a*
        // trailing expression, and it must not be `()` (which would wrongly force the whole
        // `try` to have type unit). `halt` is polymorphic like `assert false` but reports a
        // Dafny-shaped message rather than an OCaml Assert_failure, matching EmitAbsurd.
        EmitAbsurdExpression("function did not return a value", tryBlock);
      } else if (outs.Count > 0 && !suppressImplicitOutReturn) {
        EmitReturn(outs, tryBlock);
      } else if (suppressImplicitOutReturn) {
        // The framework emits the forwarding call and its return after CreateSubroutine
        // returns. Keep the syntactic tail polymorphic without mentioning the original
        // method's out variables, which are not declared in a forwarding wrapper.
        EmitAbsurdExpression("forwarding wrapper did not return", tryBlock);
      } else {
        tryBlock.WriteLine("()");
      }
      return beforeReturn;
    }

    private List<TypeArgumentInstantiation> DescriptorArguments(
      List<TypeArgumentInstantiation> typeArgs) {
      var seen = new HashSet<TypeParameter>();
      return (typeArgs ?? []).Where(argument =>
        NeedsTypeDescriptor(argument.Formal) && seen.Add(argument.Formal)).ToList();
    }

    private string DescriptorName(TypeParameter parameter) =>
      "d_td_" + EncodeIdentifier(parameter.GetCompileName(Options));

    private List<string> SubroutineFormalNames(List<TypeArgumentInstantiation> typeArgs,
      List<Formal> formals, bool hasSetterParameter = false, bool annotateFormals = true) {
      var elements = DescriptorArguments(typeArgs)
        .Select(argument => DescriptorName(argument.Formal)).ToList();
      if (hasSetterParameter) {
        elements.Add("value");
      } else {
        elements.AddRange(formals.Where(formal => !formal.IsGhost)
          .Select(formal => annotateFormals ? FormalPatternElement(formal) : IdName(formal)));
      }
      return elements;
    }

    private string SubroutineFormalsPattern(List<TypeArgumentInstantiation> typeArgs,
      List<Formal> formals, bool hasSetterParameter = false, string receiver = null,
      bool receiverAfterDescriptors = false) {
      var elements = SubroutineFormalNames(typeArgs, formals, hasSetterParameter);
      if (receiver != null) {
        elements.Insert(receiverAfterDescriptors ? DescriptorArguments(typeArgs).Count : 0, receiver);
      }
      return elements.Count switch {
        0 => "()",
        1 => elements[0],
        _ => "(" + string.Join(", ", elements) + ")"
      };
    }

    private string FormalsPattern(List<Formal> formals) {
      var names = formals.Where(f => !f.IsGhost).Select(FormalPatternElement).ToList();
      if (names.Count == 0) {
        return "()";
      } else if (names.Count == 1) {
        return names[0];
      } else {
        return "(" + string.Join(", ", names) + ")";
      }
    }

    private string RecordTypeName(string flatName, List<TypeParameter> typeParameters) {
      var arguments = typeParameters.Select(parameter =>
        TypeVarName(parameter.GetCompileName(Options))).ToList();
      return arguments.Count switch {
        0 => flatName + "_t",
        1 => arguments[0] + " " + flatName + "_t",
        _ => "(" + string.Join(", ", arguments) + ") " + flatName + "_t"
      };
    }

    // Every class/trait's record type shares the same bare (unprefixed) closure-field names for
    // its methods/functions (see CreateClass/CreateTrait), so that OCaml's type-directed field
    // disambiguation can resolve `receiver.name(args)` correctly regardless of which one
    // `receiver` is. That disambiguation needs *something* to anchor the receiver's type to,
    // though — and an otherwise-unannotated formal whose only use is a method call has nothing
    // else to go on, so it defaults to "whichever record type happened to be declared last",
    // which is wrong as often as not. So, unlike every other formal (whose type is left to
    // ordinary inference), a class/trait-typed formal gets an explicit type annotation.
    private string FormalPatternElement(Formal f) {
      var name = IdName(f);
      // Only classes/traits have the field-name-ambiguity problem (see the comment above); an
      // array (which is also, technically, a ClassLikeDecl) doesn't, and its element type might
      // be an uninstantiated generic type parameter that can't be named as an OCaml type
      // variable anyway (Dafny's mangled names aren't valid OCaml type-variable identifiers).
      return ResolveClassLikeDecl(f.Type) is ClassDecl or TraitDecl
        ? $"({name} : {TypeName(f.Type, null, f.Origin)})"
        : name;
    }

    protected override IClassWriter CreateClass(string moduleName, bool isExtern, string fullPrintName,
        List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      if (isExtern) {
        throw new UnsupportedFeatureException(tok, Feature.ExternalClasses);
      }
      var flatName = FlatName(cls);
      var classDeclaration = (TopLevelDeclWithMembers)cls;
      var typeParams = TypeParamString(typeParameters);
      var header = $"{typeParams}{flatName}_t";
      var fieldWriter = NewTypeDecl(header + " = {");
      // These four come first, in this order, on every class AND trait record: the runtime
      // reaches them positionally with Obj.field (see DafnyRuntime.reference_id/
      // reference_type_name/reference_object), because it has no single record type it could
      // name to read them by label. Do not reorder or insert ahead of them without updating
      // those three functions.
      fieldWriter.WriteLine("mutable {0}__dummy : unit;", flatName); // guarantees the record is non-empty
      fieldWriter.WriteLine("d_dafny_id : unit ref;");
      fieldWriter.WriteLine("d_dafny_type_name : string;");
      fieldWriter.WriteLine("mutable d_dafny_object : Obj.t;");
      classPrintNames[classDeclaration] = fullPrintName;
      foreach (var parameter in typeParameters.Where(NeedsTypeDescriptor)) {
        fieldWriter.WriteLine("{0} : {1} DafnyRuntime.TypeDescriptor.t;",
          DescriptorName(parameter), TypeVarName(parameter.GetCompileName(Options)));
      }
      // Every non-static method/function gets a closure field too (see EmitNew), so that a call
      // written as `receiver.name(args)` — which is how the framework compiles every instance
      // call, not just field access — resolves to a plain (and thus OCaml-native) field read.
      // Field names here are intentionally NOT flat-name-prefixed, since that's the bare name
      // the framework writes at call sites; OCaml's type-directed disambiguation resolves the
      // ambiguity with same-named fields on unrelated record types.
      foreach (var m in InstanceCallableMembers(classDeclaration)) {
        fieldWriter.WriteLine("{0} : {1};", IdName(m),
          MemberClosureFieldType(m, classDeclaration, fieldWriter));
      }
      currentBlocks.TypeBlock.Write("}");
      currentBlocks.TypeBlock.WriteLine();
      // A trait-typed reference is compiled as a *different* record type (see CreateTrait) that
      // only carries the trait's own members' closures, structurally shaped like a little vtable.
      // A class that implements one or more traits gets one upcast function per trait here, each
      // building that trait's record by picking the relevant closures back off this class's own
      // record; EmitCoercionIfNecessary calls the right one whenever this class's static type
      // needs widening to a trait type it implements.
      if (superClasses != null) {
        foreach (var superClass in superClasses.Where(t => !t.IsObject)) {
          if (superClass.NormalizeExpand() is UserDefinedType { ResolvedClass: TraitDecl traitDecl }) {
            EmitTraitUpcast(flatName, classDeclaration, traitDecl);
          }
        }
      }
      var allocatorPattern = SubroutineFormalsPattern(
        TypeArgumentInstantiation.ListFromFormals(typeParameters), []);
      classAllocators.Add(classDeclaration,
        NewValueDecl($"{flatName}{ModuleSeparator}d_new {allocatorPattern}"));
      return new ClassWriter(flatName, this, fieldWriter);
    }

    private void EmitTraitUpcast(string classFlatName, TopLevelDeclWithMembers sourceDecl,
      TraitDecl traitDecl) {
      // The compound function name below is a single identifier being *defined* in the class's
      // own file, so it needs traitDecl's raw (unqualified) flat name, not FlatName's qualified
      // one (see RawFlatName) — but building a value of the trait's record type still needs a
      // qualifier on (at least) one field if that record type lives in a different file (see
      // BuildClassInstance for the same pattern with a class's own record type).
      var traitFlat = RawFlatName(traitDecl);
      var traitQualifier = ModuleQualifier(traitDecl.EnclosingModuleDefinition);
      var sourceRecordType = RecordTypeName(classFlatName, sourceDecl.TypeArgs);
      // Record labels such as d_dafny_id and method names deliberately occur on every
      // class/trait record. Give OCaml an explicit source type here, rather than letting its
      // "last declaration wins" label disambiguation choose an unrelated record.
      var w = NewValueDecl(
        $"{classFlatName}{ModuleSeparator}__as__{traitFlat} (this : {sourceRecordType})");
      foreach (var parameter in sourceDecl.TypeArgs.Where(NeedsTypeDescriptor)) {
        var descriptor = DescriptorName(parameter);
        w.Write("let {0} = this.{0} in ", descriptor);
      }
      w.Write("{{ {0}{1}__dummy = ()", traitQualifier, traitFlat);
      w.Write("; d_dafny_id = this.d_dafny_id");
      w.Write("; d_dafny_type_name = this.d_dafny_type_name");
      w.Write("; d_dafny_object = this.d_dafny_object");
      foreach (var parameter in traitDecl.TypeArgs.Where(NeedsTypeDescriptor)) {
        var actual = sourceDecl.ParentFormalTypeParametersToActuals
          .GetValueOrDefault(parameter, new UserDefinedType(parameter));
        w.Write("; {0} = {1}", DescriptorName(parameter),
          TypeDescriptor(actual, w, parameter.Origin));
      }
      foreach (var m in InstanceCallableMembers(traitDecl)) {
        w.Write("; {0} = this.{0}", IdName(m));
      }
      foreach (var field in InstanceFields(traitDecl)) {
        var getter = TraitFieldGetter(field);
        var setter = TraitFieldSetter(field);
        if (sourceDecl is TraitDecl) {
          w.Write("; {0} = this.{0}; {1} = this.{1}", getter, setter);
        } else {
          var storage = InternalFieldPrefix + field.GetCompileName(Options);
          w.Write("; {0} = (fun () -> this.{2}); {1} = (fun value -> this.{2} <- value)",
            getter, setter, storage);
        }
      }
      w.Write(" }");
    }

    private IEnumerable<MemberDecl> InstanceCallableMembers(TopLevelDeclWithMembers cls) {
      return cls.InheritedMembers.Concat(cls.Members)
        .Where(member => !member.IsGhost && !member.IsStatic &&
                         member is Function or MethodOrConstructor or ConstantField)
        .GroupBy(member => member.GetCompileName(Options))
        .Select(group => group.Last());
    }

    private IEnumerable<Field> InstanceFields(TopLevelDeclWithMembers declaration) {
      return declaration.InheritedMembers.Concat(declaration.Members)
        .OfType<Field>()
        .Where(field => !field.IsGhost && !field.IsStatic && field is not ConstantField)
        .GroupBy(field => field.GetCompileName(Options))
        .Select(group => group.Last());
    }

    private string TraitFieldGetter(Field field) =>
      "d_field_get_" + EncodeIdentifier(field.GetCompileName(Options));

    private string TraitFieldSetter(Field field) =>
      "d_field_set_" + EncodeIdentifier(field.GetCompileName(Options));

    private List<Formal> MemberIns(MemberDecl m) =>
      m is ConstantField ? new List<Formal>() : ((MethodOrFunction)m).Ins;

    private Type MemberTypeInOwner(Type type, TopLevelDeclWithMembers owner) =>
      type.Subst(owner.ParentFormalTypeParametersToActuals);

    private string MemberResultTypeString(MemberDecl m, TopLevelDeclWithMembers owner,
      ConcreteSyntaxTree wr) {
      if (m is Field field) {
        return TypeName(MemberTypeInOwner(field.Type, owner), wr, field.Origin);
      } else if (m is Function f) {
        return TypeName(MemberTypeInOwner(f.ResultType, owner), wr, f.Origin);
      }
      var outs = ((MethodOrConstructor)m).Outs.Where(o => !o.IsGhost).ToList();
      if (outs.Count == 0) {
        return "unit";
      } else if (outs.Count == 1) {
        return TypeName(MemberTypeInOwner(outs[0].Type, owner), wr, outs[0].Origin);
      }
      return "(" + string.Join(" * ", outs.Select(o =>
        TypeName(MemberTypeInOwner(o.Type, owner), wr, o.Origin))) + ")";
    }

    private string MemberClosureFieldType(MemberDecl m, TopLevelDeclWithMembers owner,
      ConcreteSyntaxTree wr) {
      var memberDescriptors = ForTypeDescriptors(
        CombineAllTypeArguments(m), m.EnclosingClass, m, false);
      var argumentTypes = DescriptorArguments(memberDescriptors)
        .Select(argument => {
          var descriptorType = MemberTypeInOwner(argument.Actual, owner);
          return $"{TypeName(descriptorType, wr, argument.Formal.Origin)} " +
                 "DafnyRuntime.TypeDescriptor.t";
        })
        .ToList();
      argumentTypes.AddRange(MemberIns(m).Where(formal => !formal.IsGhost)
        .Select(formal => TypeName(MemberTypeInOwner(formal.Type, owner), wr, formal.Origin)));
      var argumentType = argumentTypes.Count switch {
        0 => "unit",
        1 => argumentTypes[0],
        _ => "(" + string.Join(" * ", argumentTypes) + ")"
      };
      var methodTypeParameters = (m as ICallable)?.TypeArgs ?? [];
      var quantifier = methodTypeParameters.Count == 0
        ? ""
        : string.Join(" ", methodTypeParameters.Select(parameter =>
          TypeVarName(parameter.GetCompileName(Options)))) + ". ";
      return $"{quantifier}{argumentType} -> {MemberResultTypeString(m, owner, wr)}";
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TraitDecl trait, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      if (isExtern) {
        throw new UnsupportedFeatureException(tok, Feature.ExternalClasses);
      }
      // A trait-typed reference is its own record type — essentially a vtable — carrying one
      // closure field per callable member the trait declares (not the members of any particular
      // implementing class; see EmitTraitUpcast in CreateClass for how a concrete class's record
      // gets converted to this shape). Trait fields are represented by getter/setter closures,
      // so their storage stays in the concrete object while trait-typed access remains dynamic.
      var flatName = FlatName(trait);
      var typeParams = TypeParamString(typeParameters);
      var header = $"{typeParams}{flatName}_t";
      var fieldWriter = NewTypeDecl(header + " = {");
      // Same fixed prefix as a class record, for the same reason -- see CreateClass.
      fieldWriter.WriteLine("mutable {0}__dummy : unit;", flatName);
      fieldWriter.WriteLine("d_dafny_id : unit ref;");
      fieldWriter.WriteLine("d_dafny_type_name : string;");
      fieldWriter.WriteLine("d_dafny_object : Obj.t;");
      foreach (var parameter in typeParameters.Where(NeedsTypeDescriptor)) {
        fieldWriter.WriteLine("{0} : {1} DafnyRuntime.TypeDescriptor.t;",
          DescriptorName(parameter), TypeVarName(parameter.GetCompileName(Options)));
      }
      foreach (var m in InstanceCallableMembers(trait)) {
        fieldWriter.WriteLine("{0} : {1};", IdName(m),
          MemberClosureFieldType(m, trait, fieldWriter));
      }
      foreach (var field in InstanceFields(trait)) {
        var fieldType = field.Type.Subst(trait.ParentFormalTypeParametersToActuals);
        fieldWriter.WriteLine("{0} : unit -> {1};", TraitFieldGetter(field),
          TypeName(fieldType, fieldWriter, field.Origin));
        fieldWriter.WriteLine("{0} : {1} -> unit;", TraitFieldSetter(field),
          TypeName(fieldType, fieldWriter, field.Origin));
      }
      currentBlocks.TypeBlock.Write("}");
      currentBlocks.TypeBlock.WriteLine();
      if (superClasses != null) {
        foreach (var superClass in superClasses.Where(type => !type.IsObject)) {
          if (superClass.NormalizeExpand() is UserDefinedType { ResolvedClass: TraitDecl parent }) {
            EmitTraitUpcast(flatName, trait, parent);
          }
        }
      }
      return new ClassWriter(flatName, this, fieldWriter);
    }

    // Unlike every other feature this backend supports, iterators are left unimplemented rather
    // than implemented in a simplified way: a Dafny iterator's `MoveNext` needs to *resume* the
    // iterator body right after the last `yield`, which needs either genuine coroutines (OCaml
    // 4.14, which this backend targets, has none — no effect handlers, no `yield`) or running the
    // body on a second OS thread with a hand-off protocol (Mutex/Condition) between it and the
    // caller. The latter is what a production backend without native coroutine support would
    // normally do (compare java.util.concurrent-based approaches) — but it's real concurrency
    // with real deadlock/race potential, and getting it right calls for a level of testing this
    // backend's "simple to read and maintain" design goal doesn't leave much room for. (The
    // other, non-thread-based option — eagerly running the whole iterator body up front and
    // recording every `yield`ed value into a list for `MoveNext` to hand out one at a time later —
    // would sidestep the concurrency risk, but silently hangs on an infinite iterator and
    // silently breaks any iterator whose behavior depends on caller-side state that changes
    // between `MoveNext` calls, which felt like the worse trade.) Even Java's backend, with a
    // real, mature thread implementation to build on, makes the same call.
    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(iter.Origin, Feature.Iterators);
    }

    private string TypeParamString(List<TypeParameter> typeParameters) {
      if (typeParameters == null || typeParameters.Count == 0) {
        return "";
      }
      return "(" + string.Join(", ", typeParameters.Select(tp => TypeVarName(tp.GetCompileName(Options)))) + ") ";
    }

    private static string TypeVarName(string dafnyName) => "'d_" + EncodeIdentifier(dafnyName);

    // ----- Datatypes ----------------------------------------------------------------------------

    protected override bool DatatypeDeclarationAndMemberCompilationAreSeparate => true;
    public override bool SupportsDatatypeWrapperErasure => true;

    // Raw (unqualified) constructor name: only safe to use where the constructor is guaranteed to
    // be in scope unqualified, i.e. at its own `type ... = | Ctor of ...` definition (see
    // DeclareDatatype) — everywhere else (constructing or pattern-matching a value), use CtorName,
    // which qualifies with the datatype's module if that's not the one currently being compiled.
    private string RawCtorName(DatatypeCtor ctor) =>
      EncodeCompoundIdentifier("D_ctor_", ctor.EnclosingDatatype.GetCompileName(Options),
        ctor.GetCompileName(Options));

    private string CtorName(DatatypeCtor ctor) => ModuleQualifier(ctor.ContainingModule) + RawCtorName(ctor);

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      if (dt is TupleTypeDecl) {
        return null; // Dafny tuples are OCaml tuples; no declaration needed.
      }

      var flatName = FlatName(dt);
      var typeParams = TypeParamString(dt.TypeArgs);
      var header = $"{typeParams}{flatName}_t =";
      var w = NewTypeDecl(header);
      foreach (var ctor in dt.Ctors) {
        w.Write("\n| {0}", RawCtorName(ctor));
        var nonGhost = ctor.Formals.Where(f => !f.IsGhost).ToList();
        if (nonGhost.Count > 0) {
          w.Write(" of {0}", string.Join(" * ", nonGhost.Select(f => TypeName(f.Type, w, f.Origin))));
        }
      }
      w.WriteLine();

      return new ClassWriter(flatName, this, new ConcreteSyntaxTree() /* datatypes have no mutable fields */);
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      // Newtypes are fully erased: they share the representation of their base type (see
      // ConcreteBaseType/TypeName), so there's no OCaml type to declare here. We do, however,
      // still need somewhere for any static members (e.g. a compiled witness) to live.
      var flatName = FlatName(nt);
      var cw = new ClassWriter(flatName, this, new ConcreteSyntaxTree());
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var wStmts = new ConcreteSyntaxTree();
        var witness = NewValueDecl($"{flatName}{ModuleSeparator}Witness ()");
        witness.Append(wStmts);
        witness.Append(Expr(nt.Witness, false, wStmts));
      }
      GenerateIsMethod(nt);
      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var flatName = FlatName(sst);
        var wStmts = new ConcreteSyntaxTree();
        var witness = NewValueDecl($"{flatName}{ModuleSeparator}Witness ()");
        witness.Append(wStmts);
        witness.Append(Expr(sst.Witness, false, wStmts));
      }
      GenerateIsMethod(sst);
    }

    private void GenerateIsMethod(RedirectingTypeDecl declaration) {
      if (!declaration.ConstraintIsCompilable) {
        return;
      }
      var sourceType = UserDefinedType.FromTopLevelDecl(declaration.Tok, (TopLevelDecl)declaration);
      var source = new Formal(declaration.Tok, "_source", sourceType, true, false, null);
      var body = CreateSubroutine(FlatName((TopLevelDecl)declaration), IsMethodName, [source], [],
        true, true, true,
        typeArgs: TypeArgumentInstantiation.ListFromFormals(declaration.TypeArgs));
      GenerateIsMethodBody(declaration, source, body);
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      // All numeric types share a single (Z.t) representation, so there's no special native info.
      name = "DafnyRuntime.Int.t";
      literalSuffix = "";
      needsCastAfterArithmetic = false;
    }

    // ----- Types ----------------------------------------------------------------------------

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      needsTypeParameter = false;
      needsTypeDescriptor = cl switch {
        DatatypeDecl => true,
        TraitDecl => isStatic || lookasideBody,
        _ => isStatic
      };
    }

    protected override bool NeedsTypeDescriptor(TypeParameter tp) => true;

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      var normalized = type.NormalizeExpandKeepConstraints();
      if (normalized is UserDefinedType { ResolvedClass: TypeParameter parameter }) {
        return DescriptorName(parameter);
      }
      var defaultValue = TypeInitializationValue(type, wr, tok, false, true);
      var equality = EqualityFunction(type);
      var rendered = ExprToString(type, ConcreteSyntaxTree.Create($"__value")).ToString();
      return "{ DafnyRuntime.TypeDescriptor.default = (fun () -> " + defaultValue + "); " +
             "equal = " + equality + "; " +
             "to_string = (fun __value -> " + rendered + ") }";
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl member = null) {
      Contract.Assume(type != null);
      var xType = DatatypeWrapperEraser.SimplifyType(Options, type).NormalizeExpand();
      if (xType is TypeProxy) {
        // Not "'_dafny_unknown": OCaml reserves the leading-underscore spelling for the weak
        // type variables it prints itself, and rejects it in source ("The type variable name
        // '_dafny_unknown is not allowed in programs").
        return "'d_unknown";
      } else if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return "int";
      } else if (xType is IntType or BigOrdinalType) {
        return "DafnyRuntime.Int.t";
      } else if (xType is RealType) {
        return "DafnyRuntime.Real.t";
      } else if (xType is BitvectorType) {
        return "DafnyRuntime.Int.t";
      } else if (xType.AsNewtype is { } newtypeDecl) {
        return TypeName(newtypeDecl.ConcreteBaseType(xType.TypeArgs), wr, tok, member);
      } else if (xType.IsObjectQ) {
        // `object` carries only the physical identity of the reference widened into it. Obj.t
        // can hold either a class's identity token or an array itself without changing that
        // identity; option supplies Dafny's null value.
        return "Obj.t option";
      } else if (xType.IsArrayType) {
        var at = xType.AsArrayType;
        var elType = UserDefinedType.ArrayElementType(xType);
        var representation = at.Dims == 1
          ? TypeName(elType, wr, tok) + " array"
          : TypeName(elType, wr, tok) + " DafnyRuntime.ArrayN.t";
        // As with classes, use one representation for nullable and statically non-null array
        // references so all array operations and coercions compose uniformly.
        return representation + " option";
      } else if (xType is UserDefinedType udt) {
        if (udt is ArrowType arrow) {
          var argumentType = arrow.Arity switch {
            0 => "unit",
            1 => TypeName(arrow.Args[0], wr, tok),
            _ => "(" + string.Join(" * ", arrow.Args.Select(arg => TypeName(arg, wr, tok))) + ")"
          };
          return $"({argumentType} -> {TypeName(arrow.Result, wr, tok)})";
        }
        if (udt.ResolvedClass is TupleTypeDecl tuple) {
          var componentTypes = SelectNonGhost(tuple, udt.TypeArgs);
          return componentTypes.Count switch {
            0 => "unit",
            1 => TypeName(componentTypes[0], wr, tok),
            _ => "(" + string.Join(" * ", componentTypes.Select(component => TypeName(component, wr, tok))) + ")"
          };
        }
        var baseName = TypeName_UDT(FullTypeName(udt, member), udt, wr, tok);
        // Every class reference — `C` (non-null; ResolvedClass is a NonNullTypeDecl) or `C?`
        // (nullable; ResolvedClass is the class itself) alike — is a `'a option`, with `null`
        // compiling to `None` (see EmitNull/EmitNew and the class comment). It would be more
        // precise to make only `C?` optional, but the framework compiles every instance call as
        // `(receiver)<accessor><name>(args)` with no hook to conditionally coerce the receiver
        // first, so both need the same representation for InstanceClassAccessor's unwrapping
        // pipeline to type-check uniformly.
        if (udt.ResolvedClass is ClassLikeDecl or NonNullTypeDecl) {
          return baseName + " option";
        }
        // A co-inductive datatype is a `Lazy.t` of the corresponding variant (see
        // EmitDatatypeValue/EmitConstructorCheck/EmitDestructor); since a constructor's fields
        // reference the type the same way any other value of it would (via TypeName, right
        // here), a self-referencing field is automatically already wrapped too, without needing
        // any special-casing of *which* fields are the recursive ones.
        return udt.ResolvedClass is CoDatatypeDecl ? baseName + " Lazy.t" : baseName;
      } else if (xType is SetType st) {
        return TypeName(st.Arg, wr, tok) + " list";
      } else if (xType is SeqType seq) {
        return TypeName(seq.Arg, wr, tok) + " array";
      } else if (xType is MultiSetType ms) {
        return "(" + TypeName(ms.Arg, wr, tok) + " * DafnyRuntime.Int.t) list";
      } else if (xType is MapType mt) {
        return "(" + TypeName(mt.Domain, wr, tok) + " * " + TypeName(mt.Range, wr, tok) + ") list";
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs,
      ConcreteSyntaxTree wr, IOrigin tok, bool omitTypeArguments) {
      return TypeNameFromParts(fullCompileName, typeArgs, wr, tok);
    }

    private string TypeNameFromParts(string fullCompileName, List<Type> typeArgs, ConcreteSyntaxTree wr, IOrigin tok) {
      if (typeArgs == null || typeArgs.Count == 0) {
        return fullCompileName;
      }
      if (typeArgs.Count == 1) {
        return TypeName(typeArgs[0], wr, tok) + " " + fullCompileName;
      }
      return "(" + string.Join(", ", typeArgs.Select(t => TypeName(t, wr, tok))) + ") " + fullCompileName;
    }

    internal override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl member) {
      if (member is { IsStatic: true, EnclosingClass: not null }) {
        // Static members are inherited in Dafny, but there is only one generated OCaml value:
        // the one owned by the declaration that introduced the member.
        return FlatName(member.EnclosingClass);
      }
      // Companion values (witnesses, constraint predicates, static members) belong to the
      // redirecting declaration itself even though its runtime value representation is erased.
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is UserDefinedType udt && udt.ResolvedClass != null) {
        return FlatName(udt.ResolvedClass);
      }
      return TypeName(type, wr, tok, member);
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      Contract.Assume(udt != null);
      var cl = udt.ResolvedClass;
      if (cl is TypeParameter tp) {
        return TypeVarName(tp.GetCompileName(Options));
      }
      if (cl is TupleTypeDecl) {
        return ""; // handled specially: tuples don't need a type name suffix
      }
      return FlatName(cl) + "_t";
    }

    private string ArrayDefaultValue(ArrayClassDecl ac) =>
      ac.Dims == 1
        ? "Some [||]"
        : $"Some {{ DafnyRuntime.ArrayN.dims = [|{string.Join("; ",
          Enumerable.Repeat("0", ac.Dims))}|]; data = [||] }}";

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IOrigin tok,
      bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      if (usePlaceboValue) {
        return "Obj.magic 0";
      }
      return TypeInitializationValue(type, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors,
        new Dictionary<(DatatypeDecl, string), string>());
    }

    private string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IOrigin tok,
      bool constructTypeParameterDefaultsFromTypeDescriptors,
      Dictionary<(DatatypeDecl, string), string> coDefaults) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is UserDefinedType { ResolvedClass: DatatypeDecl wrapper } wrapperType &&
          DatatypeWrapperEraser.IsErasableDatatypeWrapper(
            Options, wrapper, out var coreDestructor)) {
        var substitution = TypeParameter.SubstitutionMap(wrapper.TypeArgs, wrapperType.TypeArgs);
        return TypeInitializationValue(coreDestructor.Type.Subst(substitution), wr, tok,
          constructTypeParameterDefaultsFromTypeDescriptors, coDefaults);
      }
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "68"; // Dafny's specified auto-initialization value is 'D'
      } else if (xType is IntType or BigOrdinalType or BitvectorType) {
        return "DafnyRuntime.Int.zero";
      } else if (xType is RealType) {
        return "DafnyRuntime.Real.zero";
      } else if (xType is SetType) {
        return "[]";
      } else if (xType is MultiSetType) {
        return "[]";
      } else if (xType is SeqType) {
        return "[||]";
      } else if (xType is MapType) {
        return "[]";
      }

      if (xType is not UserDefinedType udt) {
        throw new InvalidOperationException(
          $"OCaml default-value lowering does not handle {xType.GetType().Name}: {xType}");
      }
      var cl = udt.ResolvedClass;
      if (cl == null) {
        throw new InvalidOperationException($"OCaml default-value lowering found an unresolved type: {xType}");
      }
      if (cl is TypeParameter or AbstractTypeDecl) {
        if (cl is TypeParameter parameter && constructTypeParameterDefaultsFromTypeDescriptors) {
          return $"({DescriptorName(parameter)}).DafnyRuntime.TypeDescriptor.default ()";
        }
        return "Obj.magic 0";
      } else if (cl is NewtypeDecl ntd) {
        if (ntd.Witness != null) {
          return $"({FlatName(ntd)}{ModuleSeparator}Witness ())";
        }
        return TypeInitializationValue(ntd.ConcreteBaseType(udt.TypeArgs), wr, tok,
          constructTypeParameterDefaultsFromTypeDescriptors, coDefaults);
      } else if (cl is SubsetTypeDecl std) {
        if (std.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          return $"({FlatName(std)}{ModuleSeparator}Witness ())";
        } else if (std.WitnessKind == SubsetTypeDecl.WKind.Special) {
          if (ArrowType.IsPartialArrowTypeName(std.Name)) {
            // OCaml function values are not option-wrapped. A partial arrow's Dafny default is
            // null, so use a unique, non-callable runtime marker of the function type.
            return "Obj.magic DafnyRuntime.null_function_marker";
          } else if (ArrowType.IsTotalArrowTypeName(std.Name)) {
            var rangeDefault = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok,
              constructTypeParameterDefaultsFromTypeDescriptors, coDefaults);
            return $"(fun _ -> {rangeDefault})";
          } else if (((NonNullTypeDecl)std).Class is ArrayClassDecl ac1) {
            return ArrayDefaultValue(ac1);
          } else {
            // Even though the type is non-null, the compiler sometimes still needs *a* bit
            // pattern to lay down before the real (verified-safe) initialization happens.
            return "None";
          }
        } else {
          return TypeInitializationValue(std.RhsWithArgument(udt.TypeArgs), wr, tok,
            constructTypeParameterDefaultsFromTypeDescriptors, coDefaults);
        }
      } else if (cl is ArrayClassDecl ac2) {
        // A direct ArrayClassDecl denotes the nullable form. The non-null subset type was
        // handled above and gets the empty-array auto-initialization value.
        return "None";
      } else if (cl is ClassLikeDecl) {
        // Reached only for a nullable `C?` (a non-null `C` is a SubsetTypeDecl, handled above).
        return "None";
      } else if (cl is ArrowTypeDecl) {
        // The unconstrained/general arrow type has null as its Dafny default. As with partial
        // arrows above, it is represented by a plain OCaml function and needs a placeholder.
        return "Obj.magic DafnyRuntime.null_function_marker";
      } else if (cl is DatatypeDecl dt) {
        if (dt is TupleTypeDecl ttd) {
          if (ttd.NonGhostDims == 0) {
            return "()";
          }
          return "(" + string.Join(", ", SelectNonGhost(ttd, udt.TypeArgs).Select(t =>
            TypeInitializationValue(t, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors,
              coDefaults))) + ")";
        }
        var groundingCtor = dt.GetGroundingCtor();
        var nonGhost = groundingCtor.Formals.Where(f => !f.IsGhost).ToList();
        var typeSubstitution = dt.TypeArgs.Zip(udt.TypeArgs)
          .ToDictionary(pair => pair.First, pair => pair.Second);
        var coKey = (dt, string.Join("|", udt.TypeArgs.Select(argument => argument.ToString())));
        if (dt is CoDatatypeDecl && coDefaults.TryGetValue(coKey, out var existingDefault)) {
          return existingDefault;
        }
        var recursiveName = $"__dafny_co_default_{coDefaults.Count}";
        if (dt is CoDatatypeDecl) {
          coDefaults.Add(coKey, recursiveName);
        }
        var value = nonGhost.Count == 0
          ? CtorName(groundingCtor)
          : $"{CtorName(groundingCtor)} ({string.Join(", ", nonGhost.Select(f =>
            TypeInitializationValue(f.Type.Subst(typeSubstitution), wr, tok,
              constructTypeParameterDefaultsFromTypeDescriptors, coDefaults)))})";
        if (dt is not CoDatatypeDecl) {
          return value;
        }
        coDefaults.Remove(coKey);
        return $"(let rec {recursiveName} = lazy ({value}) in {recursiveName})";
      } else {
        throw new InvalidOperationException(
          $"OCaml default-value lowering does not handle declaration {cl.GetType().Name}: {cl.FullName}");
      }
    }

    // ----- Declarations -------------------------------------------------------------

    protected override void DeclareExternType(AbstractTypeDecl d, Expression compileTypeHint, ConcreteSyntaxTree wr) {
      Error(GeneratorErrors.ErrorId.c_abstract_type_cannot_be_compiled_extern, d.Origin, wr,
        "Abstract type ('{0}') cannot be compiled to OCaml.", d.FullName);
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IOrigin tok, bool isInParam, ConcreteSyntaxTree wr) {
      return false; // formals are named-only; see FormalsPattern
    }

    private readonly HashSet<string> predeclaredTailOutputs = new();
    private Function predeclaredTailFunction;

    private bool IsPredeclaredTailResult(string name) =>
      name == IdProtect("_hresult") &&
      enclosingFunction != null &&
      enclosingFunction == predeclaredTailFunction;

    protected override void DeclareLocalVar(string name, Type type, IOrigin tok, bool leaveRoomForRhs, string rhs, ConcreteSyntaxTree wr) {
      if (IsPredeclaredTailResult(name)) {
        if (leaveRoomForRhs) {
          Contract.Assert(rhs == null);
          wr.Write(name);
        } else if (rhs != null) {
          wr.WriteLine("{0} := ({1});", name, rhs);
        }
        return;
      }
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);
        // The generic assignment hook appends " := rhs;" immediately after this method.
        wr.WriteLine("let {0} = ref (Obj.magic 0) in", name);
        wr.Write(name);
      } else {
        // A declaration without an initializer is not a request for Dafny's semantic default;
        // verified code assigns it before any read. Use an unobservable placeholder instead.
        wr.WriteLine("let {0} = ref ({1}) in", name, rhs ?? "Obj.magic 0");
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IOrigin tok, ConcreteSyntaxTree wr) {
      if (IsPredeclaredTailResult(name)) {
        wr.Write("{0} := (", name);
        var predeclaredRhs = wr.Fork();
        wr.WriteLine(");");
        return predeclaredRhs;
      }
      wr.Write("let {0} = ref (", name);
      var w = wr.Fork();
      wr.WriteLine(") in");
      return w;
    }

    protected override bool UseReturnStyleOuts(MethodOrConstructor m, int nonGhostOutCount) => true;

    protected override void DeclareOutCollector(string collectorVarName, ConcreteSyntaxTree wr) {
      wr.Write("let {0} = ref (", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, IOrigin tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
      if (predeclaredTailOutputs.Remove(name)) {
        wr.WriteLine("{0} := ({1});", name, rhs ?? "Obj.magic 0");
      } else {
        DeclareLocalVar(name, type, tok, false, rhs, wr);
      }
    }

    protected override void EmitCallReturnOuts(List<string> outTmps, ConcreteSyntaxTree wr) {
      wr.Write("{0} := ", Util.Comma(outTmps));
    }

    protected override void EmitMultiReturnTuple(List<Formal> outs, List<Type> outTypes,
      List<string> outTmps, IOrigin methodToken, ConcreteSyntaxTree wr) {
      var returnWriter = EmitReturnExpr(wr);
      var separator = "";
      for (int i = 0, runtimeIndex = 0; i < outs.Count; i++) {
        if (outs[i].IsGhost) {
          continue;
        }
        returnWriter.Write(separator);
        var valueWriter = EmitCoercionIfNecessary(
          outs[i].Type, outTypes[runtimeIndex], methodToken, returnWriter);
        valueWriter.Write("!{0}", outTmps[runtimeIndex]);
        separator = ", ";
        runtimeIndex++;
      }
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, ConcreteSyntaxTree wr) {
      wr.WriteLine(") in");
      if (actualOutParamNames.Count == 1) {
        wr.WriteLine("{0} := !{1};", actualOutParamNames[0], outCollector);
      } else {
        for (var i = 0; i < actualOutParamNames.Count; i++) {
          wr.WriteLine("{0} := (let ({1}) = !{2} in {3});", actualOutParamNames[i],
            string.Join(", ", Enumerable.Range(0, actualOutParamNames.Count).Select(j => j == i ? "__x" : "_")),
            outCollector, "__x");
        }
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IOrigin tok, ConcreteSyntaxTree wr) {
      // Type arguments are erased; OCaml's inference figures them out.
    }


    // Local variables (and everything that reuses the generic assignment machinery, e.g.
    // accumulator variables) are `ref` cells; assignment is `:=`, not `=`.
    protected override string AssignmentSymbol =>
      enclosingDeclaration is Field field && thisContext != null &&
      field.EnclosingClass != thisContext
        ? " <- "
        : " := ";

    protected override (ConcreteSyntaxTree wArray, ConcreteSyntaxTree wRhs) EmitArrayUpdate(List<Action<ConcreteSyntaxTree>> indices, Type elementType, ConcreteSyntaxTree wr) {
      if (indices.Count == 1) {
        var wArray1 = EmitArraySelect(indices, elementType, wr);
        wr.Write(" <- ");
        var wRhs1 = wr.Fork();
        return (wArray1, wRhs1);
      }
      wr.Write("(DafnyRuntime.ArrayN.set (DafnyRuntime.unwrap (");
      var wArr = wr.Fork();
      wr.Write(")) [|");
      wr.Comma("; ", indices, idx => idx(wr));
      wr.Write("|] (");
      var wRhs = wr.Fork();
      wr.Write("))");
      return (wArr, wRhs);
    }

    protected override void EmitNull(Type type, ConcreteSyntaxTree wr) {
      wr.Write("None");
    }

    private TopLevelDeclWithMembers ResolveClassLikeDecl(Type type) {
      var userDefined = type as UserDefinedType ??
                        type?.NormalizeExpandKeepConstraints() as UserDefinedType ??
                        type?.NormalizeExpand() as UserDefinedType;
      var cl = userDefined?.ResolvedClass;
      if (cl is NonNullTypeDecl nnd) {
        cl = nnd.Class;
      }
      return cl as TopLevelDeclWithMembers;
    }

    private readonly HashSet<string> activeDatatypeCoercions = new();

    // A trait-typed reference is compiled as a different (smaller) record type than any of its
    // implementing classes (see CreateTrait); converting between the two needs an explicit
    // upcast (see EmitCoercionIfNecessary), so this deliberately does NOT match a plain class.
    protected override ConcreteSyntaxTree EmitCoercionIfNecessary(Type from, Type to, IOrigin tok, ConcreteSyntaxTree wr, Type toOrig = null) {
      if (from is null || to is null) {
        return wr;
      }
      var simplifiedArrowFrom = DatatypeWrapperEraser.SimplifyType(Options, from);
      var simplifiedArrowTo = DatatypeWrapperEraser.SimplifyType(Options, to);
      if (simplifiedArrowFrom.AsArrowType is { } fromArrow &&
          simplifiedArrowTo.AsArrowType is { } toArrow &&
          !simplifiedArrowFrom.Equals(simplifiedArrowTo)) {
        Contract.Assert(fromArrow.Args.Count == toArrow.Args.Count);
        var argumentNames =
          Enumerable.Range(0, toArrow.Args.Count).Select(i => $"__argument{i}").ToList();
        wr.Write("(let __source = (");
        var sourceWriter = wr.Fork();
        wr.Write(") in (fun {0} -> ",
          argumentNames.Count switch {
            0 => "()",
            1 => argumentNames[0],
            _ => $"({string.Join(", ", argumentNames)})"
          });
        var resultWriter = EmitCoercionIfNecessary(fromArrow.Result, toArrow.Result, tok, wr);
        resultWriter = EmitDowncastIfNecessary(fromArrow.Result, toArrow.Result, tok, resultWriter);
        resultWriter.Write("__source ");
        if (argumentNames.Count == 0) {
          resultWriter.Write("()");
        } else {
          var convertedArguments = new List<string>();
          for (var i = 0; i < argumentNames.Count; i++) {
            var converted = new ConcreteSyntaxTree();
            var argumentWriter =
              EmitCoercionIfNecessary(toArrow.Args[i], fromArrow.Args[i], tok, converted);
            argumentWriter =
              EmitDowncastIfNecessary(toArrow.Args[i], fromArrow.Args[i], tok, argumentWriter);
            argumentWriter.Write(argumentNames[i]);
            convertedArguments.Add(converted.ToString());
          }
          resultWriter.Write(argumentNames.Count == 1
            ? $"({convertedArguments[0]})"
            : $"({string.Join(", ", convertedArguments)})");
        }
        wr.Write("))");
        return sourceWriter;
      }
      if (to.NormalizeExpand().IsObjectQ && !from.NormalizeExpand().IsObjectQ &&
          (ResolveClassLikeDecl(from) is not null || from.NormalizeExpand().IsArrayType)) {
        wr.Write("(match (");
        var objectWriter = wr.Fork();
        if (from.NormalizeExpand().IsArrayType) {
          wr.Write(") with None -> None | Some __o -> Some " +
                   "(DafnyRuntime.box_object (Obj.repr __o) (Obj.repr __o)))");
        } else {
          wr.Write(") with None -> None | Some __o -> Some " +
                   "(DafnyRuntime.box_object (DafnyRuntime.reference_id __o) " +
                   "(DafnyRuntime.reference_object __o)))");
        }
        return objectWriter;
      }
      var simplifiedFrom = DatatypeWrapperEraser.SimplifyType(Options, from).NormalizeExpand();
      var simplifiedTo = DatatypeWrapperEraser.SimplifyType(Options, to).NormalizeExpand();
      if (simplifiedFrom is UserDefinedType {
            ResolvedClass: DatatypeDecl sourceDatatype
          } sourceDatatypeType &&
          ResolveClassLikeDecl(to) is TraitDecl targetTrait) {
        return EmitDatatypeTraitUpcast(sourceDatatypeType, sourceDatatype, targetTrait, tok, wr);
      }
      if (simplifiedFrom is UserDefinedType {
            ResolvedClass: DatatypeDecl fromDatatype
          } fromDatatypeType &&
          simplifiedTo is UserDefinedType {
            ResolvedClass: DatatypeDecl toDatatype
          } toDatatypeType &&
          fromDatatype == toDatatype &&
          fromDatatype is not TupleTypeDecl &&
          !fromDatatypeType.TypeArgs.SequenceEqual(toDatatypeType.TypeArgs)) {
        return EmitDatatypeCoercion(fromDatatypeType, toDatatypeType, fromDatatype, tok, wr);
      }
      if (ResolveClassLikeDecl(from) is { } fromClass
          && ResolveClassLikeDecl(to) is TraitDecl toTrait
          && fromClass != toTrait) {
        wr.Write("(match (");
        var w = wr.Fork();
        // __as__ names are single identifiers defined (unqualified) in fromClass's own file, so
        // only the whole compound name gets one qualifier, not each raw flat name separately —
        // see EmitTraitUpcast.
        wr.Write(") with None -> None | Some __o -> Some ({0}{1}{2}__as__{3} __o))",
          ModuleQualifier(fromClass.EnclosingModuleDefinition), RawFlatName(fromClass), ModuleSeparator, RawFlatName(toTrait));
        return w;
      }
      var fromCollection = from.NormalizeToAncestorType();
      var toCollection = to.NormalizeToAncestorType();
      if (fromCollection is SeqType fromSequence && toCollection is SeqType toSequence &&
          !fromSequence.Arg.Equals(toSequence.Arg)) {
        wr.Write("(Array.map (fun __element -> ");
        var elementWriter = EmitCoercionIfNecessary(fromSequence.Arg, toSequence.Arg, tok, wr);
        elementWriter = EmitDowncastIfNecessary(fromSequence.Arg, toSequence.Arg, tok, elementWriter);
        elementWriter.Write("__element");
        wr.Write(") (");
        var sourceWriter = wr.Fork();
        wr.Write("))");
        return sourceWriter;
      }
      if (fromCollection is SetType fromSet && toCollection is SetType toSet &&
          !fromSet.Arg.Equals(toSet.Arg)) {
        wr.Write("(DafnyRuntime.Set.of_list ({0}) (List.map (fun __element -> ",
          EqualityFunction(toSet.Arg));
        var elementWriter = EmitCoercionIfNecessary(fromSet.Arg, toSet.Arg, tok, wr);
        elementWriter = EmitDowncastIfNecessary(fromSet.Arg, toSet.Arg, tok, elementWriter);
        elementWriter.Write("__element");
        wr.Write(") (");
        var sourceWriter = wr.Fork();
        wr.Write(")))");
        return sourceWriter;
      }
      if (fromCollection is MultiSetType fromMultiset &&
          toCollection is MultiSetType toMultiset &&
          !fromMultiset.Arg.Equals(toMultiset.Arg)) {
        wr.Write("(DafnyRuntime.Multiset.map ({0}) (fun __element -> ",
          EqualityFunction(toMultiset.Arg));
        var elementWriter = EmitCoercionIfNecessary(fromMultiset.Arg, toMultiset.Arg, tok, wr);
        elementWriter =
          EmitDowncastIfNecessary(fromMultiset.Arg, toMultiset.Arg, tok, elementWriter);
        elementWriter.Write("__element");
        wr.Write(") (");
        var sourceWriter = wr.Fork();
        wr.Write("))");
        return sourceWriter;
      }
      if (fromCollection is MapType fromMap && toCollection is MapType toMap &&
          (!fromMap.Domain.Equals(toMap.Domain) || !fromMap.Range.Equals(toMap.Range))) {
        wr.Write("(DafnyRuntime.Map_.of_list ({0}) (List.map (fun (__key, __value) -> (",
          EqualityFunction(toMap.Domain));
        var keyWriter = EmitCoercionIfNecessary(fromMap.Domain, toMap.Domain, tok, wr);
        keyWriter = EmitDowncastIfNecessary(fromMap.Domain, toMap.Domain, tok, keyWriter);
        keyWriter.Write("__key");
        wr.Write(", ");
        var valueWriter = EmitCoercionIfNecessary(fromMap.Range, toMap.Range, tok, wr);
        valueWriter = EmitDowncastIfNecessary(fromMap.Range, toMap.Range, tok, valueWriter);
        valueWriter.Write("__value");
        wr.Write(")) (");
        var sourceWriter = wr.Fork();
        wr.Write(")))");
        return sourceWriter;
      }
      return base.EmitCoercionIfNecessary(from, to, tok, wr, toOrig);
    }

    protected override ConcreteSyntaxTree EmitDowncast(Type from, Type to, IOrigin tok,
      ConcreteSyntaxTree wr) {
      if (ResolveClassLikeDecl(to) is ClassDecl targetClass &&
          ResolveClassLikeDecl(from) != targetClass) {
        var targetOptionType = TypeName(to, null, tok);
        Contract.Assert(targetOptionType.EndsWith(" option", StringComparison.Ordinal));
        var targetRecordType = targetOptionType[..^" option".Length];
        wr.Write("(match (");
        var sourceWriter = wr.Fork();
        var backingObject = from.NormalizeExpand().IsObjectQ
          ? "DafnyRuntime.unbox_object_value __o"
          : "DafnyRuntime.reference_object __o";
        wr.Write(") with None -> None | Some __o -> Some " +
                 "((Obj.obj ({0}) : {1})))", backingObject, targetRecordType);
        return sourceWriter;
      }
      return base.EmitDowncast(from, to, tok, wr);
    }

    private ConcreteSyntaxTree EmitDatatypeCoercion(UserDefinedType fromType, UserDefinedType toType,
      DatatypeDecl datatype, IOrigin tok, ConcreteSyntaxTree wr) {
      var key = $"{datatype.FullDafnyName}:{fromType}->{toType}";
      if (!activeDatatypeCoercions.Add(key)) {
        // A recursive occurrence has the same outer representation. This fallback only cuts the
        // code-generation cycle; the enclosing lazy/variant conversion still handles every
        // immediately observable field.
        wr.Write("(Obj.magic (");
        var recursiveSource = wr.Fork();
        wr.Write("))");
        return recursiveSource;
      }

      try {
        ConcreteSyntaxTree sourceWriter;
        if (datatype is CoDatatypeDecl) {
          wr.Write("(lazy (match Lazy.force (");
          sourceWriter = wr.Fork();
          wr.Write(") with ");
        } else {
          wr.Write("(match (");
          sourceWriter = wr.Fork();
          wr.Write(") with ");
        }

        var fromSubstitution =
          TypeParameter.SubstitutionMap(datatype.TypeArgs, fromType.TypeArgs);
        var toSubstitution =
          TypeParameter.SubstitutionMap(datatype.TypeArgs, toType.TypeArgs);
        var separator = "";
        foreach (var constructor in datatype.Ctors) {
          wr.Write(separator);
          separator = " | ";
          var fields = constructor.Formals.Where(formal => !formal.IsGhost).ToList();
          var names = fields.Select((_, index) => $"__field{index}").ToList();
          var pattern = fields.Count switch {
            0 => CtorName(constructor),
            1 => $"{CtorName(constructor)} {names[0]}",
            _ => $"{CtorName(constructor)} ({string.Join(", ", names)})"
          };
          wr.Write("{0} -> ", pattern);
          if (fields.Count == 0) {
            wr.Write(CtorName(constructor));
            continue;
          }

          var convertedFields = new List<string>();
          for (var i = 0; i < fields.Count; i++) {
            var fromFieldType = fields[i].Type.Subst(fromSubstitution);
            var toFieldType = fields[i].Type.Subst(toSubstitution);
            var converted = new ConcreteSyntaxTree();
            ConcreteSyntaxTree inner;
            if (ResolveClassLikeDecl(toFieldType) is ClassDecl targetClass &&
                ResolveClassLikeDecl(fromFieldType) != targetClass) {
              // IsTargetSupertype follows Dafny's variance rules, which can hide the
              // representation-changing reference cast inside a datatype downcast.
              inner = EmitDowncast(fromFieldType, toFieldType, tok, converted);
            } else {
              inner = EmitCoercionIfNecessary(fromFieldType, toFieldType, tok, converted);
              inner = EmitDowncastIfNecessary(fromFieldType, toFieldType, tok, inner);
            }
            inner.Write(names[i]);
            convertedFields.Add(converted.ToString());
          }
          wr.Write("({0} ({1}))", CtorName(constructor), string.Join(", ", convertedFields));
        }
        wr.Write(datatype is CoDatatypeDecl ? "))" : ")");
        return sourceWriter;
      } finally {
        activeDatatypeCoercions.Remove(key);
      }
    }

    private ConcreteSyntaxTree EmitDatatypeTraitUpcast(UserDefinedType sourceType,
      DatatypeDecl sourceDatatype, TraitDecl targetTrait, IOrigin tok, ConcreteSyntaxTree wr) {
      var traitFlatName = RawFlatName(targetTrait);
      var traitQualifier = ModuleQualifier(targetTrait.EnclosingModuleDefinition);
      // The identity token below is minted fresh on every upcast, so two upcasts of the same
      // datatype value are not physically equal. That is unobservable: EqualityFunction only
      // compares trait-typed values by identity, and the resolver rejects `==` on a trait that
      // isn't a reference type ("can only be applied to expressions of types that support
      // equality"), while a datatype in turn cannot extend a reference trait. So a value built
      // here can never reach the identity comparison.
      wr.Write("(let __value = (");
      var sourceWriter = wr.Fork();
      wr.Write(") in Some {{ {0}{1}__dummy = (); d_dafny_id = ref (); " +
               "d_dafny_type_name = {2}; d_dafny_object = Obj.repr __value",
        traitQualifier, traitFlatName,
        TargetStringLiteral(
          (sourceDatatype.EnclosingModuleDefinition.TryToAvoidName
            ? ""
            : sourceDatatype.EnclosingModuleDefinition.Name + ".") +
          sourceDatatype.Name));

      foreach (var parameter in targetTrait.TypeArgs.Where(NeedsTypeDescriptor)) {
        var actual = sourceDatatype.ParentFormalTypeParametersToActuals
          .GetValueOrDefault(parameter, new UserDefinedType(parameter))
          .Subst(TypeParameter.SubstitutionMap(sourceDatatype.TypeArgs, sourceType.TypeArgs));
        wr.Write("; {0} = {1}", DescriptorName(parameter),
          TypeDescriptor(actual, wr, tok));
      }

      var implementations = InstanceCallableMembers(sourceDatatype)
        .ToDictionary(member => member.GetCompileName(Options));
      foreach (var traitMember in InstanceCallableMembers(targetTrait)) {
        var implementation = implementations.GetValueOrDefault(
          traitMember.GetCompileName(Options), traitMember);
        var memberDescriptors = ForTypeDescriptors(
          CombineAllTypeArguments(traitMember), traitMember.EnclosingClass, traitMember, false);
        var arguments = SubroutineFormalNames(
          memberDescriptors, MemberIns(traitMember), annotateFormals: false);
        var pattern = arguments.Count switch {
          0 => "()",
          1 => arguments[0],
          _ => $"({string.Join(", ", arguments)})"
        };
        var actuals = new List<string>(arguments);
        actuals.Insert(DescriptorArguments(memberDescriptors).Count, "__value");
        var application = actuals.Count switch {
          0 => "()",
          1 => actuals[0],
          _ => $"({string.Join(", ", actuals)})"
        };
        wr.Write("; {0} = (fun {1} -> {2}{3}{4} {5})",
          IdName(traitMember), pattern, FlatName(sourceDatatype), ModuleSeparator,
          IdName(implementation), application);
      }
      wr.Write(" })");
      return sourceWriter;
    }

    // Finishes a class's allocation helper after all field declarations are known.
    private void BuildClassInstance(TopLevelDeclWithMembers cl, ConcreteSyntaxTree result) {
      var flatName = RawFlatName(cl);
      result.Write(
        "(let rec this = {{ {0}__dummy = (); d_dafny_id = ref (); d_dafny_type_name = {1}; " +
        "d_dafny_object = Obj.repr ()",
        flatName, TargetStringLiteral(classPrintNames[cl]));
      foreach (var parameter in cl.TypeArgs.Where(NeedsTypeDescriptor)) {
        var descriptor = DescriptorName(parameter);
        result.Write("; {0} = {0}", descriptor);
      }
      foreach (var field in instanceFields.GetValueOrDefault(flatName, [])) {
        result.Write("; {0} = {1}", field.Name, field.Initializer);
      }
      foreach (var m in InstanceCallableMembers(cl)) {
        var memberDescriptors = ForTypeDescriptors(
          CombineAllTypeArguments(m), m.EnclosingClass, m, false);
        var arguments = SubroutineFormalNames(
          memberDescriptors, MemberIns(m), annotateFormals: false);
        // An annotation containing a method type variable makes the closure monomorphic under
        // OCaml's value restriction. Leave these allocator-local patterns unannotated; the
        // top-level callee and the universally quantified record field provide all needed types.
        var pattern = arguments.Count switch {
          0 => "()",
          1 => arguments[0],
          _ => "(" + string.Join(", ", arguments) + ")"
        };
        var application = arguments.Count == 0
          ? "this"
          : "(this, " + string.Join(", ", arguments) + ")";
        result.Write("; {0} = (fun {1} -> {2}{3}{4} {5})", IdName(m), pattern,
          flatName, ModuleSeparator, IdName(m), application);
      }
      result.Write(" } in this.d_dafny_object <- Obj.repr this; this)");
    }

    // ----- Statements -------------------------------------------------------------

    // Every statement (including these block-shaped ones) is expected to leave a trailing ";"
    // behind, since a Dafny statement list is compiled as an OCaml ";"-separated sequence (see
    // the class comment). For an if/then/else, only the very last leaf of the else-chain
    // supplies that trailing ";" — everything up through "end else" is written here, and the
    // nested statement compiler (TrStmtNonempty, called by the framework right after this
    // returns) supplies the else-branch's own "begin ... end;" (via EmitBlock, if it's a block)
    // or its own trailing ";" (if it's a single statement, e.g. another `if`).
    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      wr.Write("if (");
      guardWriter = wr.Fork();
      ConcreteSyntaxTree thn;
      if (hasElse) {
        thn = wr.NewBlock(") then begin", "end else", BlockStyle.Newline, BlockStyle.Space);
      } else {
        thn = wr.NewBlock(") then begin", "end;", BlockStyle.Newline, BlockStyle.Newline);
      }
      thn.Fork(0).WriteLine("();"); // ensure the branch is unit-typed even if empty; harmless otherwise
      return thn;
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      var w = wr.NewBlock("begin", "end;", BlockStyle.Newline, BlockStyle.Newline);
      w.Fork(0).WriteLine("();");
      return w;
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      // An unlabeled `break;` (EmitBreak with label == null) targets the innermost loop, however
      // it's built; wrapping the *entire* loop (not just each iteration) in a handler for it is
      // what makes that "exit the loop" rather than "skip to the next iteration".
      DeclareExceptionOnce("Dafny_break_loop");
      wr.Write("(try while (");
      guardWriter = wr.Fork();
      var wBody = wr.NewBlock(") do", "done with Dafny_break_loop -> ());", BlockStyle.Newline, BlockStyle.Newline);
      wBody.Fork(0).WriteLine("();");
      return wBody;
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      wr.Write("DafnyRuntime.print (");
      if (arg.Type.IsStringType) {
        wr.Write("(DafnyRuntime.Seq.string_of_chars {0} (",
          UnicodeCharEnabled ? "true" : "false");
        wr.Append(Expr(arg, false, wStmts));
        wr.Write("))");
      } else {
        wr.Append(ExprToString(arg.Type, Expr(arg, false, wStmts)));
      }
      wr.WriteLine(");");
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      string resultExpr;
      if (outParams.Count == 0) {
        resultExpr = "()";
      } else if (outParams.Count == 1) {
        resultExpr = "!" + IdName(outParams[0]);
      } else {
        resultExpr = "(" + string.Join(", ", outParams.Select(o => "!" + IdName(o))) + ")";
      }
      wr.WriteLine("raise (DafnyRuntime.Return (Obj.repr ({0})));", resultExpr);
    }

    protected override ConcreteSyntaxTree EmitReturnExpr(ConcreteSyntaxTree wr) {
      wr.Write("raise (DafnyRuntime.Return (Obj.repr (");
      var w = wr.Fork();
      wr.WriteLine(")));");
      return w;
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      var exnName = (createContinueLabel ? "Dafny_continue_" : "Dafny_break_") + label;
      DeclareExceptionOnce(exnName);
      wr.Write("(try begin ");
      var w = wr.Fork();
      wr.WriteLine(" end with {0} -> ());", exnName);
      return w;
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      if (label == null) {
        DeclareExceptionOnce("Dafny_break_loop");
        wr.WriteLine("raise Dafny_break_loop;");
      } else {
        DeclareExceptionOnce($"Dafny_break_{label}");
        wr.WriteLine($"raise Dafny_break_{label};");
      }
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      DeclareExceptionOnce($"Dafny_continue_{label}");
      wr.WriteLine($"raise Dafny_continue_{label};");
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      wr.WriteLine("DafnyRuntime.halt {0};",
        TargetStringLiteral(message ?? "unexpected control point"));
    }

    // The same thing in expression position: `DafnyRuntime.halt` has type 'a, so it can stand
    // in wherever a syntactically required but unreachable trailing expression is needed.
    private void EmitAbsurdExpression(string message, ConcreteSyntaxTree wr) {
      wr.WriteLine("DafnyRuntime.halt {0}", TargetStringLiteral(message));
    }

    protected override void EmitHalt(IOrigin tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("DafnyRuntime.halt (");
      if (tok != null) {
        wr.Write(TargetStringLiteral(tok.OriginToString(Options) + ": ") + " ^ ");
      }
      if (messageExpr.Type.IsStringType) {
        wr.Write("DafnyRuntime.Seq.string_of_chars {0} (",
          UnicodeCharEnabled ? "true" : "false");
        wr.Append(Expr(messageExpr, false, wStmts));
        wr.Write(")");
      } else {
        wr.Append(ExprToString(messageExpr.Type, Expr(messageExpr, false, wStmts)));
      }
      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IOrigin tok, IVariable loopIndex, bool goingUp,
      string endVarName, List<Statement> body, List<Label> labels, ConcreteSyntaxTree wr) {
      var indexName = IdName(loopIndex);
      wr.Write(goingUp
        ? "let {0} = ref ("
        : "let {0} = ref (DafnyRuntime.Int.pred (", indexName);
      var startWriter = wr.Fork();
      wr.WriteLine(goingUp ? ") in" : ")) in");
      // Go through Int.lt/Int.ge rather than OCaml's polymorphic `<`/`>=`. Zarith registers a
      // custom comparison, so the polymorphic operators would in fact give the right answer
      // here, but they route through caml_compare and Zarith's own documentation discourages
      // them; every other comparison this backend emits already uses DafnyRuntime.Int.
      var cond = endVarName == null
        ? "true"
        : goingUp
          ? $"DafnyRuntime.Int.lt (!{indexName}, !{endVarName})"
          : $"DafnyRuntime.Int.ge (!{indexName}, !{endVarName})";
      DeclareExceptionOnce("Dafny_break_loop");
      wr.Write("(try ");
      var w = wr.NewBlock($"while ({cond}) do", "done with Dafny_break_loop -> ());",
        BlockStyle.Newline, BlockStyle.Newline);
      var loopBody = w;
      var sourceBody = EmitContinueLabel(labels, loopBody);
      Coverage.Instrument(tok, "for loop body", sourceBody);
      TrStmtList(body, sourceBody);
      loopBody.WriteLine(goingUp
        ? "{0} := DafnyRuntime.Int.succ !{0};"
        : "{0} := DafnyRuntime.Int.pred !{0};", indexName);
      return startWriter;
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      resultType = resultType.NormalizeExpand();
      var thenExpr = Expr(thn, inLetExprBody, wStmts);
      var castedThenExpr = resultType.Equals(thn.Type.NormalizeExpand()) ? thenExpr : Cast(resultType, thenExpr);
      var elseExpr = Expr(els, inLetExprBody, wStmts);
      var castedElseExpr = resultType.Equals(els.Type.NormalizeExpand()) ? elseExpr : Cast(resultType, elseExpr);
      wr.Write("(if (");
      wr.Append(Expr(guard, inLetExprBody, wStmts));
      wr.Write(") then (");
      wr.Append(castedThenExpr);
      wr.Write(") else (");
      wr.Append(castedElseExpr);
      wr.Write("))");
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, Action<ConcreteSyntaxTree> bound, ConcreteSyntaxTree wr, string start = null) {
      // Per the abstract method's contract, indexVar's type here is "the native array-index
      // type" — i.e. a plain OCaml int, unlike every other "int" in this backend (see the class
      // comment), so `bound` (typically an ArrayLength-flavored Z.t expression) needs converting.
      wr.Write("let {0} = ref ({1}) in", indexVar, start ?? "0");
      wr.WriteLine();
      wr.Write("while (!{0} < (DafnyRuntime.Int.to_int (", indexVar);
      bound(wr);
      var wBody = wr.NewBlock("))) do", "done;", BlockStyle.Newline, BlockStyle.Newline);
      var beforeIncr = wBody.Fork(0);
      wBody.WriteLine("{0} := !{0} + 1;", indexVar);
      return beforeIncr;
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      wr.WriteLine("let {0} = ref (DafnyRuntime.Int.of_int {1}) in", indexVar, start);
      var wBody = wr.NewBlock("while true do", "done;", BlockStyle.Newline, BlockStyle.Newline);
      var beforeIncr = wBody.Fork(0);
      wBody.WriteLine("{0} := DafnyRuntime.Int.mul !{0} (DafnyRuntime.Int.of_int 2);", indexVar);
      return beforeIncr;
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} := DafnyRuntime.Int.succ !{0};", varName);
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} := DafnyRuntime.Int.pred !{0};", varName);
    }

    protected override string GetQuantifierName(string bvType) => "DafnyRuntime.quantify";

    protected override (Type, Action<ConcreteSyntaxTree>) EmitIntegerRange(Type type, Action<ConcreteSyntaxTree> wLo, Action<ConcreteSyntaxTree> wHi) {
      var result = AsNativeType(type) != null ? type : new IntType();
      // The framework signals "this end of the range is unbounded" by having the bound writer
      // emit EmitNull instead of an expression (see CompileCollection's IntBoundedPool case), so
      // that is what an absent bound is compared against. Render EmitNull rather than hardcoding
      // its current output, so the two cannot drift apart.
      var absentBound = new ConcreteSyntaxTree();
      EmitNull(type, absentBound);
      var absent = absentBound.ToString().Trim();
      return (result, wr => {
        string OptionalBound(Action<ConcreteSyntaxTree> writeBound) {
          var bound = new ConcreteSyntaxTree();
          writeBound(bound);
          var rendered = bound.ToString().Trim();
          return rendered == absent ? "None" : $"Some ({rendered})";
        }
        wr.Write("(DafnyRuntime.int_range ({0}, {1}))", OptionalBound(wLo), OptionalBound(wHi));
      });
    }

    protected override void EmitBoolBoundedPool(bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.all_booleans ())");
    }

    protected override void EmitCharBoundedPool(bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.all_chars {0})", UnicodeCharEnabled ? "true" : "false");
    }

    protected override void EmitWiggleWaggleBoundedPool(bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.all_integers ())");
    }

    protected override void EmitSetBoundedPool(Expression of, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(List.to_seq (");
      wr.Append(Expr(of, inLetExprBody, wStmts));
      wr.Write("))");
    }

    protected override void EmitSubSetBoundedPool(Expression of, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.Set.all_subsets (");
      wr.Append(Expr(of, inLetExprBody, wStmts));
      wr.Write("))");
    }

    protected override void EmitMultiSetBoundedPool(Expression of, bool includeDuplicates, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.Multiset.to_seq ((");
      wr.Append(Expr(of, inLetExprBody, wStmts));
      wr.Write("), {0}))", includeDuplicates ? "true" : "false");
    }

    protected override void EmitSeqBoundedPool(Expression of, bool includeDuplicates, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (includeDuplicates) {
        wr.Write("(Array.to_seq (");
        wr.Append(Expr(of, inLetExprBody, wStmts));
        wr.Write("))");
      } else {
        var elementType = ((SeqType)of.Type.NormalizeToAncestorType()).Arg;
        wr.Write("(List.to_seq (DafnyRuntime.Set.of_list ({0}) (Array.to_list (",
          EqualityFunction(elementType));
        wr.Append(Expr(of, inLetExprBody, wStmts));
        wr.Write("))))");
      }
    }

    protected override void EmitMapBoundedPool(Expression map, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(List.to_seq (DafnyRuntime.Map_.keys (");
      wr.Append(Expr(map, inLetExprBody, wStmts));
      wr.Write(")))");
    }

    protected override void EmitDatatypeBoundedPool(IVariable bv, string propertySuffix,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      // Dafny only chooses DatatypeBoundedPool for a datatype whose values are exactly its
      // singleton (zero-runtime-argument) constructors. Recursive datatypes are not finite
      // bounds here. Materialize that small enum and expose it through the same Stdlib.Seq.t
      // interface as every other bounded pool.
      var datatype = bv.Type.NormalizeExpand() is UserDefinedType { ResolvedClass: DatatypeDecl dt }
        ? dt
        : null;
      Contract.Assert(datatype != null);
      Contract.Assert(datatype.Ctors.All(ctor => ctor.Formals.All(formal => formal.IsGhost)));
      wr.Write("(List.to_seq [");
      var separator = "";
      foreach (var constructor in datatype.Ctors) {
        wr.Write(separator);
        var value = CtorName(constructor);
        wr.Write(datatype is CoDatatypeDecl ? $"lazy ({value})" : value);
        separator = "; ";
      }
      wr.Write("])");
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IOrigin tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      // The collections this iterates are always ones built by the CompileCollection/bounded-pool
      // machinery (see the "quantifiers, comprehensions" section of the class comment), which are
      // uniformly OCaml stdlib `Seq.t` — not to be confused with DafnyRuntime.Seq (this backend's
      // representation of Dafny's own seq<T>, which is an array).
      wr.Write("Seq.iter (fun {0} -> let {0} = ref {0} in begin", tmpVarName);
      var body = wr.Fork(1);
      wr.WriteLine();
      wr.Write("end) (");
      collectionWriter = wr.Fork();
      wr.WriteLine(");");
      body.Fork(0).WriteLine("();");
      return body;
    }

    // Called only when a bounded pool's element type is wider than the bound variable's own
    // type, to filter out the values that don't belong (see MaybeInjectSubtypeConstraintWrtTraits).
    [CanBeNull]
    protected override Action<ConcreteSyntaxTree> GetSubtypeCondition(string tmpVarName, Type boundVarType, IOrigin tok, ConcreteSyntaxTree wPreconditions) {
      if (!boundVarType.IsRefType || boundVarType.IsObject || boundVarType.IsObjectQ) {
        // Nothing to check: as in the C# backend, only a reference narrowing needs a run-time
        // test here, and every reference is assignable to `object`.
        return null;
      }
      // Narrowing to a particular class or trait needs a dynamic type test, which this backend
      // does not have (see EmitTypeTest and Feature.TypeTests). Returning null here would
      // silently drop the filter and admit values of the wrong type into the comprehension —
      // a wrong answer with no diagnostic — so report the feature instead.
      throw new UnsupportedFeatureException(tok, Feature.SubtypeConstraintsInQuantifiers);
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type sourceType, bool introduceBoundVar, IOrigin tok, ConcreteSyntaxTree wr) {
      // `tmpVarName` is always itself a `ref` here (it's always the name of a lambda parameter
      // freshly shadowed by CreateLambda, or a loop variable freshly shadowed by
      // CreateForeachLoop/CreateForeachIngredientLoop — see those for why every bound name is a
      // `ref`), so it needs a `!` like any other variable read. `sourceType` and `boundVarType`
      // can differ (e.g. a two-variable comprehension where one bound variable's own inferred
      // type — from how it's used elsewhere in the comprehension — is narrower than the trait
      // type of the pool it's actually enumerated from); this is exactly what the "downcast" in
      // this method's name is for (see EmitDowncast) — every other use of `boundVarName` assumes
      // its declared (narrower) type from here on, so skipping the conversion would leave it
      // holding a value shaped like the wider type instead.
      var rhs = new ConcreteSyntaxTree();
      var rhsInner = EmitCoercionIfNecessary(sourceType, boundVarType, tok, rhs);
      rhsInner = EmitDowncastIfNecessary(sourceType, boundVarType, tok, rhsInner);
      rhsInner.Write("!{0}", tmpVarName);
      if (introduceBoundVar) {
        wr.WriteLine("let {0} = ref ({1}) in", boundVarName, rhs);
      } else {
        wr.WriteLine("{0} := ({1});", boundVarName, rhs);
      }
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      // The "ingredients" collection (see EmitEmptyTupleList/EmitAddTupleToList) is an
      // `Obj.t list ref`; the framework writes the bare ingredients-variable name directly into
      // collectionWriter, so it needs the deref here rather than at the write site.
      wr.Write("List.iter (fun {0} -> let {0} = ref {0} in begin", boundVarName);
      var body = wr.Fork(1);
      wr.WriteLine();
      wr.Write("end) (List.rev !(");
      collectionWriter = wr.Fork();
      wr.WriteLine("));");
      body.Fork(0).WriteLine("();");
      return body;
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, IOrigin tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (type.NormalizeExpand().IsObjectQ) {
        // `object` has no fields, but each allocation still needs fresh physical identity.
        wr.Write("(Some (DafnyRuntime.fresh_object ()))");
        return;
      }
      var userDefinedType = (UserDefinedType)type.NormalizeExpand();
      var declaration = ResolveClassLikeDecl(type);
      wr.Write("(Some ({0}{1}d_new (", FlatName(declaration), ModuleSeparator);
      var descriptors =
        TypeArgumentInstantiation.ListFromClass(declaration, userDefinedType.TypeArgs);
      var separator = "";
      EmitTypeDescriptorsActuals(descriptors, tok, wr, ref separator);
      if (separator.Length == 0) {
        wr.Write("()");
      }
      wr.Write(")))");
    }

    protected override void EmitNewArray(Type elementType, IOrigin tok, List<string> dimensions,
        bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var initValue = exampleElement ??
                      (mustInitialize ? DefaultValue(elementType, wr, tok, true) : "Obj.magic 0");
      if (dimensions.Count == 1) {
        wr.Write("(Some (Array.make (DafnyRuntime.Int.to_int ({0})) ({1})))",
          dimensions[0], initValue);
      } else {
        wr.Write("(Some (DafnyRuntime.ArrayN.make [|{0}|] ({1})))",
          string.Join("; ", dimensions.Select(d => $"DafnyRuntime.Int.to_int ({d})")), initValue);
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.Origin));
      } else if (e.Value == null) {
        EmitNull(e.Type, wr);
      } else if (e.Value is bool b) {
        wr.Write(b ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        wr.Write("({0})", (int)Util.UnescapedCharacters(Options, (string)e.Value, false).Single());
      } else if (e is StringLiteralExpr str) {
        wr.Write("[|");
        wr.Comma("; ", Util.UnescapedCharacters(Options, (string)str.Value, str.IsVerbatim),
          character => wr.Write("{0}", character));
        wr.Write("|]");
      } else if (e.Value is BigInteger i) {
        // Only fall back to parsing a decimal string (which happens at every evaluation) for
        // literals that don't fit OCaml's native int. int.MinValue/MaxValue rather than the
        // wider 63-bit range, so the same literal works on a 32-bit target too. The argument is
        // parenthesized because `f -5` would otherwise parse as a subtraction.
        wr.Write(int.MinValue <= i && i <= int.MaxValue
          ? $"(DafnyRuntime.Int.of_int ({i}))"
          : $"(DafnyRuntime.Int.of_string \"{i}\")");
      } else if (e.Value is BaseTypes.BigDec d) {
        wr.Write("(DafnyRuntime.Real.of_string \"{0}\")", d.ToDecimalString());
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      var unescaped = Util.UnescapedCharacters(Options, str, isVerbatim);
      var text = new System.Text.StringBuilder();
      foreach (var character in unescaped) {
        if (UnicodeCharEnabled) {
          text.Append(char.ConvertFromUtf32(character));
        } else {
          text.Append((char)character);
        }
      }
      wr.Write(TargetStringLiteral(text.ToString()));
    }

    private static string TargetStringLiteral(string value) {
      var result = new System.Text.StringBuilder("\"");
      foreach (var b in System.Text.Encoding.UTF8.GetBytes(value)) {
        switch (b) {
          case (byte)'"':
            result.Append("\\\"");
            break;
          case (byte)'\\':
            result.Append("\\\\");
            break;
          case (byte)'\n':
            result.Append("\\n");
            break;
          case (byte)'\r':
            result.Append("\\r");
            break;
          case (byte)'\t':
            result.Append("\\t");
            break;
          default:
            if (b is >= 0x20 and < 0x7F) {
              result.Append((char)b);
            } else {
              // OCaml decimal byte escapes always consume exactly three digits.
              result.Append('\\');
              result.Append(b.ToString("D3"));
            }
            break;
        }
      }
      result.Append('"');
      return result.ToString();
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, [CanBeNull] NativeType nativeType,
      bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      wr.Write("(DafnyRuntime.Int.truncate {0} (", bvType.Width);
      var middle = wr.Fork();
      wr.Write("))");
      return middle;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
      bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      var width = e0.Type.NormalizeToAncestorType().AsBitVectorType.Width;
      wr.Write("(DafnyRuntime.Int.{0} {1} (", isRotateLeft ? "rotate_left" : "rotate_right", width);
      wr.Append(Expr(e0, inLetExprBody, wStmts));
      wr.Write(") (");
      wr.Append(Expr(e1, inLetExprBody, wStmts));
      wr.Write("))");
    }

    // A `forall` *statement* that can't be sequentialized into simple nested loops (because its
    // body assigns to an array/object field that's shared across iterations in a way that would
    // change which loop iterations are even valid) is instead compiled by first collecting every
    // iteration's "ingredients" (the target location(s) and the value to assign) into a list, and
    // only then applying them. Each ingredient is a Dafny-side tuple of a few different types
    // (e.g. object, index, value) at once — an ordinary heterogeneous OCaml tuple would do the
    // job just as well, except EmitTupleSelect (below) isn't told the tuple's arity, only which
    // index it wants. So instead each ingredient is stored type-erased (`Obj.t`, via `Obj.repr`)
    // and reconstructed as an ordinary tuple only long enough to pull out one field with
    // `Obj.field`, which — unlike a `match` pattern — doesn't need to know the arity.
    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("[]");
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("{0} := Obj.repr (", ingredients);
      var w = wr.Fork();
      wr.WriteLine(") :: !{0};", ingredients);
      return w;
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      wr.Write("(Obj.magic (Obj.field !{0} {1}))", prefix, i);
    }

    protected override string IdProtect(string name) => PublicIdProtect(name);

    // Preserve every source character (including case) instead of using the collision-prone
    // "lowercase the first letter" convention. Underscores are doubled and every other
    // non-ASCII-alphanumeric UTF-16 code unit is escaped, making this mapping injective.
    private static string EncodeIdentifier(string name) {
      var encoded = new System.Text.StringBuilder();
      foreach (var ch in name) {
        if (ch is >= 'A' and <= 'Z' or >= 'a' and <= 'z' or >= '0' and <= '9') {
          encoded.Append(ch);
        } else if (ch == '_') {
          encoded.Append("__");
        } else {
          encoded.Append("_u");
          encoded.Append(((int)ch).ToString("X4"));
          encoded.Append('_');
        }
      }
      return encoded.Length == 0 ? "empty" : encoded.ToString();
    }

    // A separator alone is not enough to join encoded identifiers: "__" can itself be the
    // encoding of "_". Length-prefix every component so the compound mapping remains injective.
    private static string EncodeCompoundIdentifier(string prefix, params string[] components) {
      var result = new System.Text.StringBuilder(prefix);
      foreach (var component in components) {
        var encoded = EncodeIdentifier(component);
        result.Append(encoded.Length);
        result.Append('_');
        result.Append(encoded);
      }
      return result.ToString();
    }

    // Module source files must also be distinct on case-insensitive filesystems. Encode uppercase
    // code units instead of relying on their case, while retaining a lowercase initial basename
    // so OCaml accepts it as a compilation unit filename.
    private static string EncodeFilenameIdentifier(string name) {
      var encoded = new System.Text.StringBuilder();
      foreach (var ch in name) {
        if (ch is >= 'a' and <= 'z' or >= '0' and <= '9') {
          encoded.Append(ch);
        } else if (ch == '_') {
          encoded.Append("__");
        } else {
          encoded.Append("_u");
          encoded.Append(((int)ch).ToString("x4"));
          encoded.Append('_');
        }
      }
      return encoded.Length == 0 ? "empty" : encoded.ToString();
    }

    // Reserved prefix carried by every identifier that has been through PublicIdProtect. Dafny
    // source identifiers cannot begin with '_', so nothing in the source can collide with it.
    private const string TargetIdPrefix = "__dafny_";

    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      // Some framework paths protect an identifier that has already passed through IdName.
      // Re-prefixing is suppressed so the operation is idempotent.
      return name.StartsWith(TargetIdPrefix, StringComparison.Ordinal)
        ? name
        : TargetIdPrefix + EncodeIdentifier(name);
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember) {
      // The `this` bound inside a method body (see CreateSubroutine's header) is the bare
      // record, but every class reference elsewhere is a `'a option` (see the class comment) —
      // so wrap it back up to match, the same way any other already-in-hand object would need to
      // be if it were being passed around as a `C` value.
      // The framework itself emits inherited-field getter/setter bodies using direct record
      // syntax (`this._field`), however, so that one narrowly identified context needs the bare
      // record rather than a Dafny reference.
      var isInheritedFieldAccessor =
        enclosingDeclaration is Field field && thisContext != null &&
        field.EnclosingClass != thisContext && !callToInheritedMember;
      var inTailCallLoop = enclosingMethod is { IsTailRecursive: true } ||
                           enclosingFunction is { IsTailRecursive: true };
      var receiver = inTailCallLoop ? "!_this" : "this";
      if (inTailCallLoop && thisContext is ClassLikeDecl) {
        wr.Write(isInheritedFieldAccessor
          ? $"(DafnyRuntime.unwrap ({receiver}))"
          : receiver);
      } else {
        wr.Write(isInheritedFieldAccessor || thisContext is not ClassLikeDecl
          ? receiver
          : $"(Some {receiver})");
      }
    }

    private static readonly Regex BareIdentifier =
      new(@"^[A-Za-z_][A-Za-z0-9_']*$");

    // Every local variable and formal is a `ref` cell (see the class comment), so every read
    // needs a `!`. Most callers pass EmitIdentifier a genuine bare name — but a few (e.g. the
    // base class's ArrayLvalueImpl, by way of StabilizeExpr) instead pass it an already-fully
    // rendered expression (of a "stable" receiver, which they treat as interchangeable with a
    // bare name because for every *other* backend the two happen to render identically). Only
    // add the `!` when `ident` actually looks like a bare name, so re-dispatch like that doesn't
    // double-dereference.
    protected override void EmitIdentifier(string ident, ConcreteSyntaxTree wr) {
      wr.Write(BareIdentifier.IsMatch(ident) ? "!" + ident : ident);
    }

    protected override ILvalue IdentLvalue(string var) {
      if (var == "_this") {
        // TrTailCall adds EndStmt itself after assigning the receiver. The ordinary
        // SimpleLvalue path also adds one, which becomes OCaml's phrase terminator [;;] and
        // accidentally ends the function before the formal-parameter assignments.
        return new ILvalueImpl(this, wr => wr.Write(var), (wr, rhs) => {
          wr.Write("{0} := ", var);
          rhs(wr);
        }, appendTerminator: false);
      }
      return base.IdentLvalue(var);
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      if (dt is TupleTypeDecl) {
        wr.Write(arguments.Length == 0 ? "()" : "({0})", arguments);
        return;
      }
      var ctorName = CtorName(dtv.Ctor);
      var value = arguments.Length == 0 ? ctorName : $"({ctorName} ({arguments}))";
      // A codatatype value is always a Lazy.t (see TypeName): `lazy` defers building this
      // constructor value until it's actually forced, which is what makes it safe to build an
      // infinite value co-recursively (e.g. `Cons(x, Tail())` where `Tail` calls back into the
      // very function being defined) instead of looping forever right here.
      wr.Write(dt is CoDatatypeDecl ? $"(lazy {value})" : value);
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType, out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = (string)idParam;
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          // idParam is null for `array<T>.Length` (single dimension); an int (the dimension
          // index) for `array2<T>.Length0`/`.Length1`/etc. (see EmitMemberSelect, which handles
          // the common `arr.Length` case directly; this one only matters for the framework's own
          // internal uses of ArrayLength, e.g. compiling a multi-dimensional array's initializer).
          if (idParam == null) {
            preString = id == SpecialField.ID.ArrayLengthInt
              ? "(DafnyRuntime.Seq.length_int (DafnyRuntime.unwrap ("
              : "(DafnyRuntime.Seq.length (DafnyRuntime.unwrap (";
            postString = ")))";
          } else {
            preString = id == SpecialField.ID.ArrayLengthInt
              ? "(DafnyRuntime.ArrayN.length_int (DafnyRuntime.unwrap ("
              : "(DafnyRuntime.ArrayN.length (DafnyRuntime.unwrap (";
            postString = $")) {(int)idParam})";
          }
          break;
        case SpecialField.ID.Floor:
          preString = "(DafnyRuntime.Real.floor (";
          postString = "))";
          break;
        case SpecialField.ID.Keys:
          preString = "(DafnyRuntime.Map_.keys (";
          postString = "))";
          break;
        case SpecialField.ID.Values:
          var valueType = ((MapType)receiverType.NormalizeToAncestorType()).Range;
          preString = $"(DafnyRuntime.Map_.values ({EqualityFunction(valueType)}) (";
          postString = "))";
          break;
        case SpecialField.ID.Items:
          // `Map_.items` returns the map's own (key, value) association list unchanged — already
          // exactly the `Set` representation (a duplicate-free list; unique since map keys are).
          preString = "(DafnyRuntime.Map_.items (";
          postString = "))";
          break;
        case SpecialField.ID.Reads:
        case SpecialField.ID.Modifies:
        case SpecialField.ID.New:
          compiledName = "";
          break;
        case SpecialField.ID.IsLimit:
          // A compiled ORDINAL is always a plain natural number (see TypeName's BigOrdinalType
          // case), so it's a limit ordinal exactly when it's 0 — the same convention Go's
          // Ord.IsLimitOrd uses.
          preString = "(DafnyRuntime.Int.equal DafnyRuntime.Int.zero (";
          postString = "))";
          break;
        case SpecialField.ID.IsSucc:
          preString = "(DafnyRuntime.Int.compare (";
          postString = ") DafnyRuntime.Int.zero > 0)";
          break;
        case SpecialField.ID.Offset:
          // The ordinal *is* its own offset above the nearest limit ordinal (0), since it's just
          // a natural number.
          compiledName = "";
          break;
        case SpecialField.ID.IsNat:
          // Every compiled ORDINAL is a natural number; evaluate (and discard) the receiver for
          // its side effects, matching Go's Ord.IsNatOrd.
          preString = "(let _ = ";
          postString = " in true)";
          break;
        default:
          Contract.Assert(false);
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
      Type expectedType, string additionalCustomParameter = null, bool internalAccess = false) {
      switch (DatatypeWrapperEraser.GetMemberStatus(Options, member)) {
        case DatatypeWrapperEraser.MemberCompileStatus.Identity:
          return SimpleLvalue(obj);
        case DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue:
          return StringLvalue("true");
      }

      if (member is DatatypeDestructor dtor && dtor.EnclosingClass is TupleTypeDecl ttd) {
        var nonGhostFormals = ttd.Ctors[0].Formals.Where(formal => !formal.IsGhost).ToList();
        var idx = ttd.NonGhostDims == 1
          ? 0
          : nonGhostFormals.IndexOf(dtor.CorrespondingFormals[0]);
        return SimpleLvalue(wr => {
          if (ttd.NonGhostDims == 1) {
            obj(wr);
          } else {
            wr.Write("(let ({0}) = ", string.Join(", ", Enumerable.Range(0, ttd.NonGhostDims).Select(i => i == idx ? "__t" : "_")));
            obj(wr);
            wr.Write(" in __t)");
          }
        });
      } else if (member is DatatypeDiscriminator disc) {
        var ctor0 = FindCtor(disc);
        return SimpleLvalue(wr => {
          wr.Write("(match ");
          WriteMatchSource(obj, ctor0?.EnclosingDatatype, wr);
          wr.Write(" with {0} -> true | _ -> false)", CtorPatternWildcard(ctor0));
        });
      } else if (member is SpecialField sf2 && sf2 is DatatypeDestructor dtor2) {
        return SimpleLvalue(wr => {
          var datatype = dtor2.EnclosingCtors[0].EnclosingDatatype;
          var sourceType = objType.NormalizeExpand() is UserDefinedType sourceDatatypeType &&
                           sourceDatatypeType.ResolvedClass == datatype
            ? dtor2.CorrespondingFormals[0].Type.Subst(
              TypeParameter.SubstitutionMap(datatype.TypeArgs, sourceDatatypeType.TypeArgs))
            : dtor2.Type;
          var valueWriter = EmitCoercionIfNecessary(sourceType, expectedType, dtor2.Origin, wr);
          valueWriter = EmitDowncastIfNecessary(sourceType, expectedType, dtor2.Origin, valueWriter);
          valueWriter.Write("(match ");
          WriteMatchSource(obj, datatype, valueWriter);
          valueWriter.Write(" with ");
          var separator = "";
          for (var i = 0; i < dtor2.EnclosingCtors.Count; i++) {
            valueWriter.Write(separator);
            separator = " | ";
            valueWriter.Write("{0} -> {1}", DestructorPattern(dtor2, i, out var varName), varName);
          }
          valueWriter.Write(" | _ -> DafnyRuntime.halt \"unexpected constructor\")");
        });
      } else if (member is SpecialField sf3) {
        // A plain *read* of a SpecialField (e.g. `arr.Length`) doesn't stop here — see the
        // `MemberSelectExpr` case in SinglePassCodeGenerator.Expression.cs, which calls
        // GetSpecialFieldInfo itself, writes preStr, THEN calls EmitMemberSelect (i.e. lands
        // here) to render the object alone, and finally writes postStr. So when GetSpecialFieldInfo
        // reports a non-empty preStr/postStr for this field, that wrapping already happened
        // (or, for a non-read use of this ILvalue, wasn't wanted); either way this only needs to
        // render the object itself here.
        GetSpecialFieldInfo(sf3.SpecialId, sf3.IdParam, objType, out var compiledName, out _, out _);
        if (compiledName == "") {
          return SimpleLvalue(obj);
        }
        return SuffixLvalue(obj, ".{0}", compiledName);
      } else if (!member.IsStatic && NeedsCustomReceiverNotTrait(member)) {
        var companion = TypeName_Companion(objType, null, member.Origin, member);
        Action<ConcreteSyntaxTree> topLevelMember =
          wr => wr.Write("{0}{1}{2}", companion, ModuleSeparator, IdName(member));
        if (member is ConstantField) {
          return SimpleLvalue(wr => {
            topLevelMember(wr);
            wr.Write("(");
            var descriptors = ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false);
            var separator = "";
            EmitTypeDescriptorsActuals(descriptors, member.Origin, wr, ref separator);
            wr.Write(separator);
            obj(wr);
            wr.Write(")");
          });
        }

        Contract.Assert(additionalCustomParameter != null);
        return CustomReceiverCallableTearOff(topLevelMember,
          wr => EmitIdentifier(additionalCustomParameter, wr), member, typeArgs);
      } else if (member is ConstantField && !member.IsStatic && !internalAccess) {
        var recv = Unwrapped(obj);
        return SimpleLvalue(wr => {
          recv(wr);
          wr.Write(".{0} ()", IdName(member));
        });
      } else if (member is Field f && !member.IsStatic) {
        if (ResolveClassLikeDecl(objType) is TraitDecl) {
          var traitReceiver = Unwrapped(obj);
          return new ILvalueImpl(this, wr => {
            traitReceiver(wr);
            wr.Write(".{0} ()", TraitFieldGetter(f));
          }, (wr, rhs) => {
            traitReceiver(wr);
            wr.Write(".{0} (", TraitFieldSetter(f));
            rhs(wr);
            wr.Write(")");
          });
        }
        var cl = member.EnclosingClass;
        var receiverClass = ResolveClassLikeDecl(objType);
        var fieldName = member is ConstantField && internalAccess || receiverClass != cl
          ? InternalFieldPrefix + member.GetCompileName(Options)
          : RawFlatName(cl) + ModuleSeparator + IdName(member);
        var recv = Unwrapped(obj);
        return new ILvalueImpl(this, wr => {
          recv(wr);
          wr.Write(".{0}", fieldName);
        }, (wr, rhs) => {
          recv(wr);
          wr.Write(".{0} <- (", fieldName);
          rhs(wr);
          wr.Write(")");
        });
      } else if (member.IsStatic) {
        var companion = TypeName_Companion(objType, null, member.Origin, member);
        var flatMemberName = $"{companion}{ModuleSeparator}{IdName(member)}";
        if (member is ConstantField) {
          return SimpleLvalue(wr => {
            wr.Write("({0} (", flatMemberName);
            var descriptors = ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false);
            var separator = "";
            EmitTypeDescriptorsActuals(descriptors, member.Origin, wr, ref separator);
            if (separator.Length == 0) {
              wr.Write("()");
            }
            wr.Write("))");
          });
        }
        if (member is Field) {
          return SimpleLvalue(wr => wr.Write("!({0})", flatMemberName));
        }
        return CallableTearOff(
          wr => wr.Write(flatMemberName), member, typeArgs);
      } else {
        // A non-static function/method being referenced/torn off as a value: every class
        // instance carries a closure field per instance member (see CreateClass/EmitNew), so
        // this is just an ordinary field read.
        var recv = Unwrapped(obj);
        return CallableTearOff(wr => {
          recv(wr);
          wr.Write(".{0}", IdName(member));
        }, member, typeArgs);
      }
    }

    private ILvalue CustomReceiverCallableTearOff(Action<ConcreteSyntaxTree> callable,
      Action<ConcreteSyntaxTree> receiver, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs) {
      var descriptors = ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false);
      var formals = ((MethodOrFunction)member).Ins.Where(formal => !formal.IsGhost).ToList();
      return SimpleLvalue(wr => {
        wr.Write("(fun {0} -> ", FormalsPattern(((MethodOrFunction)member).Ins));
        callable(wr);
        wr.Write("(");
        var separator = "";
        EmitTypeDescriptorsActuals(descriptors, member.Origin, wr, ref separator);
        wr.Write(separator);
        receiver(wr);
        separator = ", ";
        foreach (var formal in formals) {
          wr.Write(separator);
          wr.Write(IdName(formal));
        }
        wr.Write("))");
      });
    }

    private ILvalue CallableTearOff(Action<ConcreteSyntaxTree> callable, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs) {
      var descriptors = ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false);
      if (DescriptorArguments(descriptors).Count == 0) {
        return SimpleLvalue(callable);
      }
      var formals = ((MethodOrFunction)member).Ins;
      return SimpleLvalue(wr => {
        var pattern = FormalsPattern(formals);
        wr.Write("(fun {0} -> (", pattern);
        callable(wr);
        wr.Write(") (");
        var separator = "";
        EmitTypeDescriptorsActuals(descriptors, member.Origin, wr, ref separator);
        foreach (var formal in formals.Where(formal => !formal.IsGhost)) {
          wr.Write(separator);
          wr.Write(IdName(formal));
          separator = ", ";
        }
        if (separator.Length == 0) {
          wr.Write("()");
        }
        wr.Write("))");
      });
    }

    // Every class reference is a `'a option` (see the class comment), so reading a field or
    // tearing off a method/function value off of one first needs to unwrap it — the same way
    // InstanceClassAccessor does for a plain call.
    private Action<ConcreteSyntaxTree> Unwrapped(Action<ConcreteSyntaxTree> obj) {
      return wr => {
        wr.Write("(DafnyRuntime.unwrap (");
        obj(wr);
        wr.Write("))");
      };
    }

    private DatatypeCtor FindCtor(DatatypeDiscriminator disc) {
      // `disc.IdParam` is "is_<ctor's compile name>" (see ModuleDefinition.AddDiscriminators),
      // not the bare constructor name.
      var idParam = disc.IdParam.ToString();
      return disc.EnclosingClass is DatatypeDecl dt
        ? dt.Ctors.First(c => idParam == "is_" + c.GetCompileName(Options))
        : null;
    }

    // A codatatype value is a Lazy.t (see TypeName); pattern-matching against its constructor
    // needs to force it first.
    private void WriteMatchSource(Action<ConcreteSyntaxTree> obj, DatatypeDecl dt, ConcreteSyntaxTree wr) {
      if (dt is CoDatatypeDecl) {
        wr.Write("(Lazy.force ");
        obj(wr);
        wr.Write(")");
      } else {
        obj(wr);
      }
    }

    private string CtorPatternWildcard(DatatypeCtor ctor) {
      if (ctor == null) {
        return "_";
      }
      var nonGhost = ctor.Formals.Count(f => !f.IsGhost);
      return nonGhost == 0 ? CtorName(ctor) : $"{CtorName(ctor)} _";
    }

    private string DestructorPattern(DatatypeDestructor dtor, int constructorIndex, out string varName) {
      varName = "__x";
      var ctor = dtor.EnclosingCtors[constructorIndex];
      var nonGhost = ctor.Formals.Where(f => !f.IsGhost).ToList();
      var idx = nonGhost.FindIndex(f => f == dtor.CorrespondingFormals[constructorIndex]);
      if (nonGhost.Count == 1) {
        return CtorName(ctor) + " " + varName;
      }
      var vn = varName;
      return CtorName(ctor) + " (" + string.Join(", ", nonGhost.Select((_, i) => i == idx ? vn : "_")) + ")";
    }

    // Per the abstract method's contract (see ArrayLvalueImpl), these indices are always
    // *already* of "the native array-index type" — a plain OCaml int here — unlike every other
    // "int" in this backend (see the class comment): either because they came from
    // ArrayIndexToNativeInt (which does the Z.t -> int conversion), or because they're already a
    // native-int loop variable straight out of CreateForLoop. So, unlike the Expression-based
    // overload below, these do NOT need an extra DafnyRuntime.Int.to_int.
    protected override ConcreteSyntaxTree EmitArraySelect(List<Action<ConcreteSyntaxTree>> indices, Type elmtType, ConcreteSyntaxTree wr) {
      if (indices.Count == 1) {
        wr.Write("(DafnyRuntime.unwrap (");
        var w = wr.Fork();
        wr.Write(")).(");
        indices[0](wr);
        wr.Write(")");
        return w;
      }
      wr.Write("(DafnyRuntime.ArrayN.get (DafnyRuntime.unwrap (");
      var wArr = wr.Fork();
      wr.Write(")) [|");
      wr.Comma("; ", indices, idx => idx(wr));
      wr.Write("|])");
      return wArr;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (indices.Count == 1) {
        wr.Write("(DafnyRuntime.unwrap (");
        var w = wr.Fork();
        wr.Write(")).(DafnyRuntime.Int.to_int (");
        wr.Append(Expr(indices[0], inLetExprBody, wStmts));
        wr.Write("))");
        return w;
      }
      wr.Write("(DafnyRuntime.ArrayN.get (DafnyRuntime.unwrap (");
      var wArr = wr.Fork();
      wr.Write(")) [|");
      wr.Comma("; ", indices, idx => {
        wr.Write("DafnyRuntime.Int.to_int (");
        wr.Append(Expr(idx, inLetExprBody, wStmts));
        wr.Write(")");
      });
      wr.Write("|])");
      return wArr;
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.Int.to_int (");
      wr.Append(Expr(expr, inLetExprBody, wStmts));
      wr.Write("))");
    }

    // An array index destined for the Action<ConcreteSyntaxTree>-based EmitArraySelect/
    // EmitArrayUpdate overload above needs converting from Z.t to a plain OCaml int (the "native
    // array-index type") exactly once, here — not again in EmitArraySelect/EmitArrayUpdate
    // themselves, since some of those indices come in already-native (a raw loop variable out of
    // CreateForLoop) rather than through this conversion.
    protected override string ArrayIndexToNativeInt(string arrayIndex, Type fromType) {
      var value = BareIdentifier.IsMatch(arrayIndex) ? "!" + arrayIndex : arrayIndex;
      return $"(DafnyRuntime.Int.to_int ({value}))";
    }

    // The reverse conversion: some framework code needs to turn a native-int array index (e.g. a
    // CreateForLoop loop variable) back into an ordinary Dafny int (Z.t) — for example to pass it
    // to a user-written `array-initializer` function, which expects a Z.t argument like any other
    // Dafny function.
    protected override void EmitArrayIndexToInt(ConcreteSyntaxTree wr, out ConcreteSyntaxTree wIndex) {
      wr.Write("(DafnyRuntime.Int.of_int (");
      wIndex = wr.Fork();
      wr.Write("))");
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (source.Type.NormalizeToAncestorType() is MapType) {
        var mapType = (MapType)source.Type.NormalizeToAncestorType();
        wr.Write("(DafnyRuntime.Map_.get ({0}) ((", EqualityFunction(mapType.Domain));
        // `index`'s static type can be narrower than the map's domain (e.g. a bound variable
        // whose own inferred type is a subtype, matching some other constraint on it) — needs
        // the same coercion EmitIndexCollectionUpdate already applies below.
        wr.Append(CoercedExpr(index, mapType.Domain, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (source.Type.NormalizeToAncestorType() is MultiSetType) {
        var multisetType = (MultiSetType)source.Type.NormalizeToAncestorType();
        wr.Write("(DafnyRuntime.Multiset.multiplicity ({0}) (",
          EqualityFunction(multisetType.Arg));
        wr.Append(CoercedExpr(index, multisetType.Arg, inLetExprBody, wStmts));
        wr.Write(") (");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write("))");
      } else {
        wr.Write("(DafnyRuntime.Seq.select ((");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write(")))");
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (resultCollectionType is MapType) {
        wr.Write("(DafnyRuntime.Map_.update ({0}) ((",
          EqualityFunction(((MapType)resultCollectionType).Domain));
        wr.Append(CoercedExpr(index, ((MapType)resultCollectionType).Domain,
          inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(CoercedExpr(value, resultCollectionType.ValueArg, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (resultCollectionType is MultiSetType) {
        wr.Write("(DafnyRuntime.Multiset.update ({0}) ((",
          EqualityFunction(((MultiSetType)resultCollectionType).Arg));
        wr.Append(CoercedExpr(index, ((MultiSetType)resultCollectionType).Arg,
          inLetExprBody, wStmts));
        wr.Write("), (");
        // A multiset update's value is the new multiplicity, not another element.
        wr.Append(Expr(value, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(")))");
      } else {
        wr.Write("(DafnyRuntime.Seq.update ((");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(CoercedExpr(value, resultCollectionType.ValueArg, inLetExprBody, wStmts));
        wr.Write(")))");
      }
    }

    // Used for a single-array-index update where the source/index/value are supplied piecemeal
    // (out parameters) rather than as Expressions — currently only by the "ingredients" forall
    // machinery above (EmitSeqSelect, always with nativeIndex: true). The default implementation
    // is C-style `source[index] = value`; this is `source.(index) <- value` instead.
    protected override void EmitIndexCollectionUpdate(Type sourceType, out ConcreteSyntaxTree wSource, out ConcreteSyntaxTree wIndex, out ConcreteSyntaxTree wValue, ConcreteSyntaxTree wr, bool nativeIndex) {
      wr.Write("(DafnyRuntime.unwrap (");
      wSource = wr.Fork();
      wr.Write(")).(");
      if (nativeIndex) {
        wIndex = wr.Fork();
      } else {
        wr.Write("DafnyRuntime.Int.to_int (");
        wIndex = wr.Fork();
        wr.Write(")");
      }
      wr.Write(") <- (");
      wValue = wr.Fork();
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi,
        bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      void EmitSource() {
        if (fromArray) {
          wr.Write("(DafnyRuntime.unwrap (");
        }
        wr.Append(Expr(source, inLetExprBody, wStmts));
        if (fromArray) {
          wr.Write("))");
        }
      }
      if (lo == null && hi == null) {
        wr.Write("(Array.copy (");
        EmitSource();
        wr.Write("))");
      } else if (lo == null) {
        wr.Write("(DafnyRuntime.Seq.take ((");
        EmitSource();
        wr.Write("), (");
        wr.Append(Expr(hi, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (hi == null) {
        wr.Write("(DafnyRuntime.Seq.drop ((");
        EmitSource();
        wr.Write("), (");
        wr.Append(Expr(lo, inLetExprBody, wStmts));
        wr.Write(")))");
      } else {
        wr.Write("(DafnyRuntime.Seq.sub ((");
        EmitSource();
        wr.Write("), (");
        wr.Append(Expr(lo, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(hi, inLetExprBody, wStmts));
        wr.Write(")))");
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.Seq.create (");
      wr.Append(Expr(expr.N, inLetExprBody, wStmts));
      wr.Write(") (fun __i -> (((");
      wr.Append(Expr(expr.Initializer, inLetExprBody, wStmts));
      wr.Write(") : {0}) __i)))", TypeName(expr.Initializer.Type, null, expr.Initializer.Origin));
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      var fromType = expr.E.Type.NormalizeToAncestorType();
      if (fromType is SetType) {
        wr.Write("(DafnyRuntime.Multiset.of_set (");
      } else {
        wr.Write("(DafnyRuntime.Multiset.of_seq ({0}) (",
          EqualityFunction(((SeqType)fromType).Arg));
      }
      wr.Append(Expr(expr.E, inLetExprBody, wStmts));
      wr.Write("))");
    }

    protected override void EmitApplyExpr(Type functionType, IOrigin tok, Expression function, List<Expression> arguments,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      // The explicit annotation matters for values returned through the exception-based
      // subroutine lowering: without it, OCaml may issue warning 20 and treat the following
      // application as an ignored extra argument instead of an application of the returned
      // function value.
      wr.Write("((");
      wr.Append(Expr(function, inLetExprBody, wStmts));
      wr.Write(") : {0})", TypeName(functionType, null, tok));
      var arrow = functionType.AsArrowType;
      Contract.Assert(arrow != null && arrow.Args.Count == arguments.Count);
      var argumentWriter = wr.ForkInParens();
      argumentWriter.Comma(arguments, (argument, index) =>
        argumentWriter.Append(CoercedExpr(argument, arrow.Args[index], inLetExprBody, wStmts)));
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IOrigin tok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      wr.Write("((fun {0} -> ", boundVars.Count == 0 ? "()" : boundVars.Count == 1 ? boundVars[0] : "(" + string.Join(", ", boundVars) + ")");
      var w = wr.Fork();
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      wr.Write(")");
      foreach (var boundVar in boundVars) {
        w.Write("let {0} = ref {0} in ", boundVar);
      }
      return w;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      var forced = ctor.EnclosingDatatype is CoDatatypeDecl ? $"(Lazy.force !{source})" : $"!{source}";
      wr.Write("(match {0} with {1} -> true | _ -> false)", forced, CtorPatternWildcard(ctor));
    }

    protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex,
      DatatypeCtor ctor, Func<List<Type>> getTypeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(
            Options, ctor.EnclosingDatatype, out var coreDestructor)) {
        Contract.Assert(coreDestructor.CorrespondingFormals.Count == 1);
        Contract.Assert(dtor == coreDestructor.CorrespondingFormals[0]);
        source(wr);
        return;
      } else if (ctor.EnclosingDatatype is TupleTypeDecl ttd) {
        if (ttd.NonGhostDims == 1) {
          source(wr);
        } else {
          wr.Write("(let ({0}) = ", string.Join(", ", Enumerable.Range(0, ttd.NonGhostDims).Select(i => i == formalNonGhostIndex ? "__t" : "_")));
          source(wr);
          wr.Write(" in __t)");
        }
        return;
      }
      var nonGhost = ctor.Formals.Where(f => !f.IsGhost).ToList();
      var pattern = nonGhost.Count == 1
        ? CtorName(ctor) + " __x"
        : CtorName(ctor) + " (" + string.Join(", ", nonGhost.Select((_, i) => i == formalNonGhostIndex ? "__x" : "_")) + ")";
      wr.Write("(match ");
      WriteMatchSource(source, ctor.EnclosingDatatype, wr);
      wr.Write(" with {0} -> __x | _ -> DafnyRuntime.halt \"unexpected constructor\")", pattern);
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IOrigin tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      Contract.Assert(inTypes.Count == inNames.Count);
      var parameters = inNames.Select((name, index) => untyped
        ? name
        : $"({name} : {TypeName(inTypes[index], null, tok)})").ToList();
      var pat = parameters.Count switch {
        0 => "()",
        1 => parameters[0],
        _ => $"({string.Join(", ", parameters)})"
      };
      wr.Write("(fun {0} -> ", pat);
      var body = wr.Fork();
      wr.Write(")");
      foreach (var n in inNames) {
        body.WriteLine("let {0} = ref {0} in", n);
      }
      // The lambda's body might, like a function body, be compiled as several statements each
      // potentially "returning" via EmitReturnExpr (e.g. if it pattern-matches) rather than as a
      // single expression — so it needs the same early-return handling as CreateSubroutine.
      return body.NewBlock("(try begin", "end with DafnyRuntime.Return __r -> Obj.magic __r)", BlockStyle.Newline, BlockStyle.Space);
    }

    protected override void CreateIIFE(string bvName, Type bvType, IOrigin bvTok, Type bodyType, IOrigin bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      // IIFE-bound variables follow the same representation as every other local: a ref cell.
      // EmitIdentifier will dereference them in the generated body.
      wr.Write("(let {0} = ref (", bvName);
      wrRhs = wr.Fork();
      wr.Write(") in ");
      wStmts = wr.Fork();
      wrBody = wr.Fork();
      wr.Write(")");
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IOrigin resultTok, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      // Used for e.g. a set/map comprehension's body, which (like a lambda's) may contain
      // several statements ending in an early return (here, via EmitReturnExpr, to hand back the
      // built collection) — same reasoning as CreateLambda/CreateIIFE1.
      wr.Write("((fun () -> ");
      var body = wr.Fork();
      wr.Write(") ())");
      return body.NewBlock("(try begin", "end with DafnyRuntime.Return __r -> Obj.magic __r)", BlockStyle.Newline, BlockStyle.Space);
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IOrigin resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      // Used for `var x :| P(x); Body`: an immediately-invoked function whose body searches for
      // an `x` satisfying `P` (see TrAssignSuchThat, built on CreateForeachLoop/CreateLabeledCode/
      // etc.) and then evaluates `Body`. Structurally identical to CreateLambda/CreateSubroutine's
      // bodies: possibly several statements, ending in an early return.
      wr.Write("((fun {0} -> ", bvName);
      var body = wr.Fork();
      wr.Write(") {0})", source);
      foreach (var n in new[] { bvName }) {
        body.WriteLine("let {0} = ref {0} in", n);
      }
      return body.NewBlock("(try begin", "end with DafnyRuntime.Return __r -> Obj.magic __r)", BlockStyle.Newline, BlockStyle.Space);
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("not", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          wr.Write("(DafnyRuntime.Int.lognot (");
          wr.Append(Expr(expr, inLetExprBody, wStmts));
          wr.Write("))");
          break;
        case ResolvedUnaryOp.Cardinality:
          var t = expr.Type.NormalizeToAncestorType();
          var fn = t is SetType ? "DafnyRuntime.Set.cardinality" :
            t is MultiSetType ? "DafnyRuntime.Multiset.cardinality" :
            t is MapType ? "DafnyRuntime.Map_.cardinality" : "DafnyRuntime.Seq.length";
          wr.Write("({0} (", fn);
          wr.Append(Expr(expr, inLetExprBody, wStmts));
          wr.Write("))");
          break;
        default:
          Contract.Assert(false); throw new Cce.UnreachableException();
      }
    }

    private string EqualityFunction(Type type) =>
      EqualityFunction(type, new Dictionary<TypeParameter, string>());

    private string EqualityFunction(Type leftType, Type rightType) {
      var left = DatatypeWrapperEraser.SimplifyType(Options, leftType).NormalizeExpand();
      var right = DatatypeWrapperEraser.SimplifyType(Options, rightType).NormalizeExpand();
      if (left.Equals(right)) {
        return EqualityFunction(leftType);
      }

      bool IsOptionReference(Type type) =>
        type.IsArrayType || type.IsObjectQ ||
        ResolveClassLikeDecl(type) is ClassDecl or TraitDecl;

      if (IsOptionReference(left) && IsOptionReference(right)) {
        string Identity(Type type, string name) {
          if (type.IsObjectQ) {
            return $"DafnyRuntime.unbox_object_id {name}";
          }
          if (type.IsArrayType) {
            return $"Obj.repr {name}";
          }
          return $"DafnyRuntime.reference_id {name}";
        }

        return "(fun __a __b -> match __a, __b with " +
               "None, None -> true | Some __x, Some __y -> " +
               $"{Identity(left, "__x")} == {Identity(right, "__y")} | _ -> false)";
      }

      // Non-reference operands that Dafny permits in one equality expression have a common
      // target representation (for example a constrained integer and int).
      return EqualityFunction(leftType);
    }

    private string EqualityFunction(Type type, IReadOnlyDictionary<TypeParameter, string> typeParameters) {
      var normalized = DatatypeWrapperEraser.SimplifyType(Options, type).NormalizeExpand();
      if (normalized is BoolType or CharType) {
        return "(fun __a __b -> __a = __b)";
      }
      if (normalized is IntType or BigOrdinalType or BitvectorType) {
        return "(fun __a __b -> DafnyRuntime.Int.equal __a __b)";
      }
      if (normalized is RealType) {
        return "(fun __a __b -> DafnyRuntime.Real.equal (__a, __b))";
      }
      if (normalized.IsArrowType) {
        // Dafny function values have reference identity; OCaml's structural equality raises
        // Invalid_argument when it reaches a closure.
        return "(fun __a __b -> Obj.repr __a == Obj.repr __b)";
      }
      if (normalized.AsNewtype is { } newtype) {
        return EqualityFunction(newtype.ConcreteBaseType(normalized.TypeArgs), typeParameters);
      }
      if (normalized is SetType set) {
        return $"(fun __a __b -> DafnyRuntime.Set.equal " +
               $"({EqualityFunction(set.Arg, typeParameters)}) (__a, __b))";
      }
      if (normalized is MultiSetType multiset) {
        return $"(fun __a __b -> DafnyRuntime.Multiset.equal " +
               $"({EqualityFunction(multiset.Arg, typeParameters)}) (__a, __b))";
      }
      if (normalized is SeqType sequence) {
        return $"(fun __a __b -> DafnyRuntime.Seq.equal " +
               $"({EqualityFunction(sequence.Arg, typeParameters)}) (__a, __b))";
      }
      if (normalized is MapType map) {
        return $"(fun __a __b -> DafnyRuntime.Map_.equal " +
               $"({EqualityFunction(map.Domain, typeParameters)}) " +
               $"({EqualityFunction(map.Range, typeParameters)}) (__a, __b))";
      }
      if (normalized.IsArrayType) {
        return "(fun __a __b -> DafnyRuntime.ref_eq (__a, __b))";
      }
      if (normalized.IsObjectQ) {
        return "(fun __a __b -> match __a, __b with " +
               "None, None -> true | Some __x, Some __y -> " +
               "DafnyRuntime.unbox_object_id __x == DafnyRuntime.unbox_object_id __y | _ -> false)";
      }
      if (ResolveClassLikeDecl(normalized) is ClassDecl or TraitDecl) {
        return "(fun __a __b -> match __a, __b with " +
               "None, None -> true | Some __x, Some __y -> " +
               "DafnyRuntime.reference_id __x == DafnyRuntime.reference_id __y | _ -> false)";
      }
      if (normalized.IsRefType) {
        return "(fun __a __b -> DafnyRuntime.ref_eq (__a, __b))";
      }
      if (normalized is UserDefinedType udt) {
        if (udt.ResolvedClass is TypeParameter parameter) {
          return typeParameters.GetValueOrDefault(parameter,
            $"(fun __a __b -> ({DescriptorName(parameter)}).DafnyRuntime.TypeDescriptor.equal __a __b)");
        }
        if (udt.ResolvedClass is TupleTypeDecl tuple) {
          var components = SelectNonGhost(tuple, udt.TypeArgs);
          if (components.Count == 0) {
            return "(fun _ _ -> true)";
          }
          var left = components.Select((_, i) => $"__a{i}").ToList();
          var right = components.Select((_, i) => $"__b{i}").ToList();
          var comparisons = components.Select((component, i) =>
            $"({EqualityFunction(component, typeParameters)}) {left[i]} {right[i]}");
          return $"(fun ({string.Join(", ", left)}) ({string.Join(", ", right)}) -> " +
                 $"{string.Join(" && ", comparisons)})";
        }
        if (udt.ResolvedClass is DatatypeDecl datatype) {
          return DatatypeEqualityFunction(udt, datatype, typeParameters);
        }
        if (udt.ResolvedClass is NewtypeDecl newtypeDeclaration) {
          return EqualityFunction(newtypeDeclaration.ConcreteBaseType(udt.TypeArgs), typeParameters);
        }
        if (udt.ResolvedClass is TypeSynonymDeclBase synonym) {
          return EqualityFunction(synonym.RhsWithArgument(udt.TypeArgs), typeParameters);
        }
      }
      // This is only reachable for an abstract/erased type whose descriptor wiring has not
      // supplied a more precise comparator.
      return "(fun __a __b -> __a = __b)";
    }

    private readonly Dictionary<DatatypeDecl, string> datatypeEqualityFunctions = new();

    private string DatatypeEqualityFunction(UserDefinedType type, DatatypeDecl datatype,
      IReadOnlyDictionary<TypeParameter, string> typeParameters = null) {
      typeParameters ??= new Dictionary<TypeParameter, string>();
      if (!datatypeEqualityFunctions.TryGetValue(datatype, out var rawName)) {
        rawName = RawFlatName(datatype) + ModuleSeparator + "d_equal";
        datatypeEqualityFunctions.Add(datatype, rawName);

        var savedModule = enclosingModule;
        var savedBlocks = currentBlocks;
        enclosingModule = datatype.EnclosingModuleDefinition;
        currentBlocks = moduleBlocks[enclosingModule];
        try {
          var equalityParameters = datatype.TypeArgs.ToDictionary(
            parameter => parameter,
            parameter => "d_equal_" + EncodeIdentifier(parameter.GetCompileName(Options)));
          var header = rawName;
          foreach (var parameter in datatype.TypeArgs) {
            header += " " + equalityParameters[parameter];
          }
          header += " __left __right";
          var body = NewValueDecl(header);
          body.Write("match {0}, {1} with ",
            datatype is CoDatatypeDecl ? "(Lazy.force __left)" : "__left",
            datatype is CoDatatypeDecl ? "(Lazy.force __right)" : "__right");
          var separator = "";
          foreach (var constructor in datatype.Ctors) {
            body.Write(separator);
            separator = " | ";
            var fields = constructor.Formals.Where(formal => !formal.IsGhost).ToList();
            if (fields.Count == 0) {
              body.Write("{0}, {0} -> true", CtorName(constructor));
              continue;
            }
            var leftNames = fields.Select((_, i) => $"__a{i}").ToList();
            var rightNames = fields.Select((_, i) => $"__b{i}").ToList();
            string Pattern(List<string> names) => fields.Count == 1
              ? $"{CtorName(constructor)} {names[0]}"
              : $"{CtorName(constructor)} ({string.Join(", ", names)})";
            body.Write("{0}, {1} -> ", Pattern(leftNames), Pattern(rightNames));
            body.Write(string.Join(" && ", fields.Select((field, i) =>
              $"({EqualityFunction(field.Type, equalityParameters)}) {leftNames[i]} {rightNames[i]}")));
          }
          body.Write(" | _ -> false");
        } finally {
          enclosingModule = savedModule;
          currentBlocks = savedBlocks;
        }
      }

      var qualifiedName = ModuleQualifier(datatype.EnclosingModuleDefinition) + rawName;
      if (datatype.TypeArgs.Count == 0) {
        return qualifiedName;
      }
      return "(" + qualifiedName + " " +
             string.Join(" ", type.TypeArgs.Select(argument =>
               $"({EqualityFunction(argument, typeParameters)})")) +
             ")";
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Type e0Type, Type e1Type, IOrigin tok, Type resultType,
      out string opString, out string preOpString, out string postOpString,
      out string callString, out string staticCallString, out bool reverseArguments,
      out bool truncateResult, out bool convertE1_to_int, out bool coerceE1,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;
      coerceE1 = false;

      var leftAncestor = e0Type.NormalizeToAncestorType();
      var rightAncestor = e1Type.NormalizeToAncestorType();

      string CoercingBinaryCollectionCall(string target) {
        string Operand(Type operandType, string name) {
          var converted = new ConcreteSyntaxTree();
          EmitCoercionIfNecessary(operandType, resultType, tok, converted).Write(name);
          return converted.ToString();
        }

        return $"(fun (__left, __right) -> {target} " +
               $"(({Operand(e0Type, "__left")}), ({Operand(e1Type, "__right")})))";
      }

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff: opString = "="; break;
        case BinaryExpr.ResolvedOpcode.Imp: preOpString = "not "; opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.Or: opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.And: opString = "&&"; break;

        case BinaryExpr.ResolvedOpcode.BitwiseAnd: staticCallString = "DafnyRuntime.Int.logand"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr: staticCallString = "DafnyRuntime.Int.logor"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor: staticCallString = "DafnyRuntime.Int.logxor"; break;

        case BinaryExpr.ResolvedOpcode.EqCommon:
          staticCallString = $"DafnyRuntime.equal ({EqualityFunction(e0Type, e1Type)})";
          break;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          preOpString = "not (";
          postOpString = ")";
          staticCallString = $"DafnyRuntime.equal ({EqualityFunction(e0Type, e1Type)})";
          break;

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          if (leftAncestor is RealType) {
            staticCallString = "DafnyRuntime.Real.lt";
          } else if (leftAncestor is IntType or BigOrdinalType or BitvectorType) {
            staticCallString = "DafnyRuntime.Int.lt";
          } else {
            opString = "<";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          if (leftAncestor is RealType) {
            staticCallString = "DafnyRuntime.Real.le";
          } else if (leftAncestor is IntType or BigOrdinalType or BitvectorType) {
            staticCallString = "DafnyRuntime.Int.le";
          } else {
            opString = "<=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          if (leftAncestor is RealType) {
            staticCallString = "DafnyRuntime.Real.ge";
          } else if (leftAncestor is IntType or BigOrdinalType or BitvectorType) {
            staticCallString = "DafnyRuntime.Int.ge";
          } else {
            opString = ">=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
          if (leftAncestor is RealType) {
            staticCallString = "DafnyRuntime.Real.gt";
          } else if (leftAncestor is IntType or BigOrdinalType or BitvectorType) {
            staticCallString = "DafnyRuntime.Int.gt";
          } else {
            opString = ">";
          }
          break;

        case BinaryExpr.ResolvedOpcode.LeftShift:
          truncateResult = true;
          staticCallString = "DafnyRuntime.Int.shift_left";
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          staticCallString = "DafnyRuntime.Int.shift_right";
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          truncateResult = true;
          if (resultType.IsCharType) {
            if (rightAncestor is CharType) {
              opString = "+";
            } else {
              staticCallString = "DafnyRuntime.Int.add_char";
            }
          } else if (resultType.NormalizeToAncestorType() is RealType) {
            staticCallString = "DafnyRuntime.Real.add";
          } else {
            staticCallString = "DafnyRuntime.Int.add";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          truncateResult = true;
          if (resultType.IsCharType) {
            if (rightAncestor is CharType) {
              opString = "-";
            } else {
              staticCallString = "DafnyRuntime.Int.sub_char";
            }
          } else if (resultType.NormalizeToAncestorType() is RealType) {
            staticCallString = "DafnyRuntime.Real.sub";
          } else {
            staticCallString = "DafnyRuntime.Int.sub";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          truncateResult = true;
          staticCallString = resultType.NormalizeToAncestorType() is RealType
            ? "DafnyRuntime.Real.mul"
            : "DafnyRuntime.Int.mul";
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          staticCallString = resultType.NormalizeToAncestorType() is RealType
            ? "DafnyRuntime.Real.div"
            : "DafnyRuntime.Int.ediv";
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          staticCallString = "DafnyRuntime.Int.erem";
          break;

        case BinaryExpr.ResolvedOpcode.SetEq:
          staticCallString = $"DafnyRuntime.Set.equal " +
                             $"({EqualityFunction(((SetType)leftAncestor).Arg, ((SetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
          staticCallString =
            $"DafnyRuntime.Multiset.equal " +
            $"({EqualityFunction(((MultiSetType)leftAncestor).Arg, ((MultiSetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.MapEq: {
            var leftMap = (MapType)leftAncestor;
            var rightMap = (MapType)rightAncestor;
            staticCallString =
              $"DafnyRuntime.Map_.equal ({EqualityFunction(leftMap.Domain, rightMap.Domain)}) " +
              $"({EqualityFunction(leftMap.Range, rightMap.Range)})";
            break;
          }
        case BinaryExpr.ResolvedOpcode.SeqEq:
          staticCallString = $"DafnyRuntime.Seq.equal " +
                             $"({EqualityFunction(((SeqType)leftAncestor).Arg, ((SeqType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.SetNeq:
          preOpString = "not ("; postOpString = ")";
          staticCallString = $"DafnyRuntime.Set.equal " +
                             $"({EqualityFunction(((SetType)leftAncestor).Arg, ((SetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
          preOpString = "not ("; postOpString = ")";
          staticCallString =
            $"DafnyRuntime.Multiset.equal " +
            $"({EqualityFunction(((MultiSetType)leftAncestor).Arg, ((MultiSetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.MapNeq: {
            preOpString = "not ("; postOpString = ")";
            var leftMap = (MapType)leftAncestor;
            var rightMap = (MapType)rightAncestor;
            staticCallString =
              $"DafnyRuntime.Map_.equal ({EqualityFunction(leftMap.Domain, rightMap.Domain)}) " +
              $"({EqualityFunction(leftMap.Range, rightMap.Range)})";
            break;
          }
        case BinaryExpr.ResolvedOpcode.SeqNeq:
          preOpString = "not ("; postOpString = ")";
          staticCallString = $"DafnyRuntime.Seq.equal " +
                             $"({EqualityFunction(((SeqType)leftAncestor).Arg, ((SeqType)rightAncestor).Arg)})";
          break;

        case BinaryExpr.ResolvedOpcode.ProperSubset:
          staticCallString =
            $"DafnyRuntime.Set.is_proper_subset " +
            $"({EqualityFunction(((SetType)leftAncestor).Arg, ((SetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          staticCallString =
            $"DafnyRuntime.Multiset.is_proper_subset " +
            $"({EqualityFunction(((MultiSetType)leftAncestor).Arg, ((MultiSetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.Subset:
          staticCallString =
            $"DafnyRuntime.Set.is_subset " +
            $"({EqualityFunction(((SetType)leftAncestor).Arg, ((SetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          staticCallString =
            $"DafnyRuntime.Multiset.is_subset " +
            $"({EqualityFunction(((MultiSetType)leftAncestor).Arg, ((MultiSetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.Superset:
          staticCallString =
            $"DafnyRuntime.Set.is_subset " +
            $"({EqualityFunction(((SetType)rightAncestor).Arg, ((SetType)leftAncestor).Arg)})";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
          staticCallString =
            $"DafnyRuntime.Multiset.is_subset " +
            $"({EqualityFunction(((MultiSetType)rightAncestor).Arg, ((MultiSetType)leftAncestor).Arg)})";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
          staticCallString =
            $"DafnyRuntime.Set.is_proper_subset " +
            $"({EqualityFunction(((SetType)rightAncestor).Arg, ((SetType)leftAncestor).Arg)})";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          staticCallString =
            $"DafnyRuntime.Multiset.is_proper_subset " +
            $"({EqualityFunction(((MultiSetType)rightAncestor).Arg, ((MultiSetType)leftAncestor).Arg)})";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
          staticCallString =
            $"DafnyRuntime.Set.is_disjoint " +
            $"({EqualityFunction(((SetType)leftAncestor).Arg, ((SetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          staticCallString =
            $"DafnyRuntime.Multiset.is_disjoint " +
            $"({EqualityFunction(((MultiSetType)leftAncestor).Arg, ((MultiSetType)rightAncestor).Arg)})";
          break;

        case BinaryExpr.ResolvedOpcode.InSet:
          staticCallString =
            $"DafnyRuntime.Set.mem ({EqualityFunction(e0Type, ((SetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.InMultiSet:
          staticCallString =
            $"DafnyRuntime.Multiset.mem ({EqualityFunction(e0Type, ((MultiSetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.InMap:
          staticCallString =
            $"DafnyRuntime.Map_.has_key ({EqualityFunction(e0Type, ((MapType)rightAncestor).Domain)})";
          break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
          preOpString = "not ("; postOpString = ")";
          staticCallString =
            $"DafnyRuntime.Set.mem ({EqualityFunction(e0Type, ((SetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
          preOpString = "not ("; postOpString = ")";
          staticCallString =
            $"DafnyRuntime.Multiset.mem ({EqualityFunction(e0Type, ((MultiSetType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "not ("; postOpString = ")";
          staticCallString =
            $"DafnyRuntime.Map_.has_key ({EqualityFunction(e0Type, ((MapType)rightAncestor).Domain)})";
          break;

        case BinaryExpr.ResolvedOpcode.Union:
          staticCallString = CoercingBinaryCollectionCall(
            $"DafnyRuntime.Set.union ({EqualityFunction(((SetType)resultType.NormalizeToAncestorType()).Arg)})");
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          staticCallString = CoercingBinaryCollectionCall(
            $"DafnyRuntime.Multiset.union ({EqualityFunction(((MultiSetType)resultType.NormalizeToAncestorType()).Arg)})");
          break;
        case BinaryExpr.ResolvedOpcode.MapMerge:
          staticCallString = CoercingBinaryCollectionCall(
            $"DafnyRuntime.Map_.merge ({EqualityFunction(((MapType)resultType.NormalizeToAncestorType()).Domain)})");
          break;
        case BinaryExpr.ResolvedOpcode.Intersection:
          staticCallString = CoercingBinaryCollectionCall(
            $"DafnyRuntime.Set.intersect ({EqualityFunction(((SetType)resultType.NormalizeToAncestorType()).Arg)})");
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          staticCallString = CoercingBinaryCollectionCall(
            $"DafnyRuntime.Multiset.intersect ({EqualityFunction(((MultiSetType)resultType.NormalizeToAncestorType()).Arg)})");
          break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
          staticCallString = CoercingBinaryCollectionCall(
            $"DafnyRuntime.Set.difference ({EqualityFunction(((SetType)resultType.NormalizeToAncestorType()).Arg)})");
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          staticCallString = CoercingBinaryCollectionCall(
            $"DafnyRuntime.Multiset.difference ({EqualityFunction(((MultiSetType)resultType.NormalizeToAncestorType()).Arg)})");
          break;
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          staticCallString =
            $"DafnyRuntime.Map_.subtract ({EqualityFunction(((MapType)leftAncestor).Domain)})";
          break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          staticCallString =
            $"DafnyRuntime.Seq.is_proper_prefix " +
            $"({EqualityFunction(((SeqType)leftAncestor).Arg, ((SeqType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          staticCallString =
            $"DafnyRuntime.Seq.is_prefix " +
            $"({EqualityFunction(((SeqType)leftAncestor).Arg, ((SeqType)rightAncestor).Arg)})";
          break;
        case BinaryExpr.ResolvedOpcode.Concat:
          staticCallString = CoercingBinaryCollectionCall("DafnyRuntime.Seq.concat");
          break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          staticCallString =
            $"DafnyRuntime.Seq.contains ({EqualityFunction(((SeqType)rightAncestor).Arg)})";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "not ("; postOpString = ")";
          staticCallString =
            $"DafnyRuntime.Seq.contains ({EqualityFunction(((SeqType)rightAncestor).Arg)})";
          reverseArguments = true;
          break;

        default:
          Contract.Assert(false); throw new Cce.UnreachableException();
      }
    }

    // A tail-recursive method/function is compiled by wrapping its body in a `while true` loop:
    // the call site (TrTailCall, in the base class) reassigns the formal `ref`s and then "jumps
    // to the start" by raising Tailcall, which is caught right around the loop body, causing the
    // `while` to simply run again with the (now updated) formal values. Normal, non-tail-call
    // completion of the body raises the stdlib's `Exit` to escape the loop instead.
    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      predeclaredTailOutputs.Clear();
      predeclaredTailFunction = member as Function;
      if (!member.IsStatic) {
        wr.WriteLine(thisContext is ClassLikeDecl
          ? "let _this = ref (Some this) in"
          : "let _this = ref this in");
      }
      if (member is MethodOrConstructor method) {
        foreach (var output in method.Outs.Where(output => !output.IsGhost)) {
          var outputName = IdName(output);
          predeclaredTailOutputs.Add(outputName);
          wr.WriteLine("let {0} = ref (Obj.magic 0) in", outputName);
        }
      }
      // Optimized return expressions can declare their hidden result temporary inside the
      // retry loop while emitting a syntactically unreachable final return just outside it.
      // Give that final expression a correctly scoped placeholder; every real completion
      // raises DafnyRuntime.Return from inside the loop. This hook is called only for members
      // that the framework has already classified as tail-recursive.
      if (member is Function) {
        wr.WriteLine("let {0} = ref (Obj.magic 0) in", IdProtect("_hresult"));
      }
      wr.Write("(try ");
      var outerBody = wr.NewBlock("while true do", "done", BlockStyle.Newline, BlockStyle.Newline);
      wr.WriteLine("with Exit -> ());");
      return outerBody.NewBlock("(try begin", "raise Exit end with DafnyRuntime.Tailcall -> ())", BlockStyle.Newline, BlockStyle.Newline);
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("raise DafnyRuntime.Tailcall;");
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write("(DafnyRuntime.Int.equal {0} DafnyRuntime.Int.zero)",
        BareIdentifier.IsMatch(varName) ? "!" + varName : varName);
    }

    protected override void EmitConversionExpr(Expression fromExpr, Type fromType, Type toType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var fromT = fromType.NormalizeToAncestorType();
      var toT = toType.NormalizeToAncestorType();
      if (fromT.IsCharType && toT.IsNumericBased(Type.NumericPersuasion.Real)) {
        wr.Write("(DafnyRuntime.Real.of_bigint (DafnyRuntime.Int.of_int (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (fromT.IsCharType && toT.IsNumericBased(Type.NumericPersuasion.Int)) {
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write(" |> DafnyRuntime.Int.of_int");
      } else if ((fromT.IsNumericBased(Type.NumericPersuasion.Int) || fromT.IsBigOrdinalType ||
                  fromT.IsBitVectorType) && toT.IsCharType) {
        wr.Write("(DafnyRuntime.Int.to_int (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write("))");
      } else if ((fromT.IsNumericBased(Type.NumericPersuasion.Int) || fromT.IsBigOrdinalType ||
                  fromT.IsBitVectorType) &&
                 toT.IsNumericBased(Type.NumericPersuasion.Real)) {
        wr.Write("(DafnyRuntime.Real.of_bigint (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write("))");
      } else if (fromT.IsNumericBased(Type.NumericPersuasion.Real) && toT.IsCharType) {
        wr.Write("(DafnyRuntime.Int.to_int (DafnyRuntime.Real.floor (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (fromT.IsNumericBased(Type.NumericPersuasion.Real) &&
                 (toT.IsNumericBased(Type.NumericPersuasion.Int) || toT.IsBigOrdinalType ||
                  toT.IsBitVectorType)) {
        wr.Write("(DafnyRuntime.Real.floor (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write("))");
      } else {
        // Most remaining numeric conversions are identities because they share Z.t. For
        // representation-changing datatype, collection, and arrow casts, however, route
        // through the regular variance/downcast machinery.
        var converted = EmitCoercionIfNecessary(fromType, toType, fromExpr.Origin, wr);
        converted = EmitDowncastIfNecessary(fromType, toType, fromExpr.Origin, converted);
        converted.Append(Expr(fromExpr, inLetExprBody, wStmts));
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IOrigin tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.TypeTests);
    }

    protected override void EmitIsIntegerTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(source.Origin, Feature.TypeTests);
    }

    protected override void EmitIsUnicodeScalarValueTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(source.Origin, Feature.TypeTests);
    }

    protected override void EmitIsInIntegerRange(Expression source, BigInteger lo, BigInteger hi, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(source.Origin, Feature.TypeTests);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IOrigin tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (ct is SetType) {
        wr.Write("(DafnyRuntime.Set.of_list ({0}) [", EqualityFunction(ct.Arg));
        wr.Comma("; ", elements, e => wr.Append(CoercedExpr(e, ct.Arg, inLetExprBody, wStmts)));
        wr.Write("])");
      } else if (ct is MultiSetType) {
        wr.Write("(DafnyRuntime.Multiset.of_seq ({0}) [|", EqualityFunction(ct.Arg));
        wr.Comma("; ", elements, e => wr.Append(CoercedExpr(e, ct.Arg, inLetExprBody, wStmts)));
        wr.Write("|])");
      } else {
        Contract.Assert(ct is SeqType);
        wr.Write("[|");
        wr.Comma("; ", elements, e => wr.Append(CoercedExpr(e, ct.Arg, inLetExprBody, wStmts)));
        wr.Write("|]");
      }
    }

    protected override void EmitMapDisplay(MapType mt, IOrigin tok, List<MapDisplayEntry> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.Map_.of_list ({0}) [", EqualityFunction(mt.Domain));
      wr.Comma("; ", elements, p => {
        wr.Write("(");
        wr.Append(CoercedExpr(p.A, mt.Domain, inLetExprBody, wStmts));
        wr.Write(", ");
        wr.Append(CoercedExpr(p.B, mt.Range, inLetExprBody, wStmts));
        wr.Write(")");
      });
      wr.Write("])");
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      DeclareLocalVar(collectionName, null, null, false, "[]", wr);
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      DeclareLocalVar(collectionName, null, null, false, "[]", wr);
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("{0} := (", collName);
      wr.Append(Expr(elmt, inLetExprBody, wStmts));
      wr.WriteLine(") :: !{0};", collName);
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IOrigin tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      // The framework writes the key into the returned writer itself (right after this call
      // returns); `term` is the *value* expression, which only we know how to render.
      var wStmts = wr.Fork();
      wr.Write("{0} := (", collName);
      var wKey = wr.Fork();
      wr.Write(", ");
      wr.Append(Expr(term, inLetExprBody, wStmts));
      wr.WriteLine(") :: !{0};", collName);
      return wKey;
    }

    protected override void GetCollectionBuilder_Build(CollectionType ct, IOrigin tok, string collName,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmt) {
      if (ct is SetType) {
        wr.Write("(DafnyRuntime.Set.of_list ({0}) (List.rev !{1}))", EqualityFunction(ct.Arg),
          collName);
      } else if (ct is MapType map) {
        wr.Write("(DafnyRuntime.Map_.of_list ({0}) (List.rev !{1}))",
          EqualityFunction(map.Domain), collName);
      } else {
        wr.Write("!{0}", collName);
      }
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(Seq.return (");
      wr.Append(Expr(e, inLetExprBody, wStmts));
      wr.Write("))");
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      // DafnyRuntime.Halt (see EmitHalt) carries a plain OCaml string; haltMessageVarName is a
      // Dafny `string` (seq<char>), so it needs converting on the way in, same as every other
      // local variable it needs to be wrapped in a `ref` (see the class comment).
      wr.WriteLine("(try begin");
      var tryBody = wr.Fork(1);
      TrStmt(body, tryBody);
      wr.WriteLine("end with DafnyRuntime.Halt __haltMsg -> begin");
      var recovery = wr.Fork(1);
      recovery.WriteLine("let {0} = ref (DafnyRuntime.Seq.of_string {1} __haltMsg) in",
        haltMessageVarName, UnicodeCharEnabled ? "true" : "false");
      TrStmt(recoveryBody, recovery);
      wr.WriteLine("end);");
    }

    // ----- print/toString ------------------------------------------------------------------

    // Since OCaml has no runtime type reflection, printing is done by generating, at each call
    // site, an expression that converts the (statically known) Dafny type to a string.
    private ConcreteSyntaxTree ExprToString(Type type, ConcreteSyntaxTree valueExpr) {
      var t = DatatypeWrapperEraser.SimplifyType(Options, type).NormalizeExpand();
      var result = new ConcreteSyntaxTree();
      if (t is BoolType) {
        result.Write("(if (");
        result.Append(valueExpr);
        result.Write(") then \"true\" else \"false\")");
      } else if (t is CharType) {
        result.Write(UnicodeCharEnabled
          ? "(DafnyRuntime.Char_.to_literal ("
          : "(DafnyRuntime.Char_.to_string (");
        result.Append(valueExpr);
        result.Write("))");
      } else if (t is IntType or BigOrdinalType or BitvectorType) {
        result.Write("(DafnyRuntime.Int.to_string (");
        result.Append(valueExpr);
        result.Write("))");
      } else if (t is RealType) {
        result.Write("(DafnyRuntime.Real.to_string (");
        result.Append(valueExpr);
        result.Write("))");
      } else if (t.IsArrowType) {
        result.Write("(if Obj.repr (");
        result.Append(valueExpr);
        result.Write(") == DafnyRuntime.null_function_marker then \"null\" else \"<function>\")");
      } else if (t.AsNewtype is { } ntd) {
        return ExprToString(ntd.ConcreteBaseType(t.TypeArgs), valueExpr);
      } else if (t.IsArrayType) {
        result.Write("(match ");
        result.Append(valueExpr);
        result.Write(" with None -> \"null\" | Some _ -> \"<array>\")");
      } else if (t is SeqType seqT && seqT.Arg.NormalizeExpand() is CharType) {
        if (UnicodeCharEnabled) {
          result.Write("(\"[\" ^ String.concat \", \" (Array.to_list " +
                       "(Array.map DafnyRuntime.Char_.to_literal (");
          result.Append(valueExpr);
          result.Write("))) ^ \"]\")");
        } else {
          result.Write("(DafnyRuntime.Seq.string_of_chars false (");
          result.Append(valueExpr);
          result.Write("))");
        }
      } else if (t is SeqType seqT2) {
        result.Write("(\"[\" ^ String.concat \", \" (Array.to_list (Array.map (fun __v -> ");
        result.Append(ExprToString(seqT2.Arg, ConcreteSyntaxTree.Create($"__v")));
        result.Write(") (");
        result.Append(valueExpr);
        result.Write("))) ^ \"]\")");
      } else if (t is SetType setT) {
        result.Write("(\"{\" ^ String.concat \", \" (List.map (fun __v -> ");
        result.Append(ExprToString(setT.Arg, ConcreteSyntaxTree.Create($"__v")));
        result.Write(") (");
        result.Append(valueExpr);
        result.Write(")) ^ \"}\")");
      } else if (t is MultiSetType msT) {
        result.Write("(\"multiset{\" ^ String.concat \", \" (List.concat_map (fun (__v, __n) -> List.init (DafnyRuntime.Int.to_int __n) (fun _ -> ");
        result.Append(ExprToString(msT.Arg, ConcreteSyntaxTree.Create($"__v")));
        result.Write(")) (");
        result.Append(valueExpr);
        result.Write(")) ^ \"}\")");
      } else if (t is MapType mapT) {
        result.Write("(\"map[\" ^ String.concat \", \" (List.map (fun (__k, __v) -> (");
        result.Append(ExprToString(mapT.Domain, ConcreteSyntaxTree.Create($"__k")));
        result.Write(") ^ \" := \" ^ (");
        result.Append(ExprToString(mapT.Range, ConcreteSyntaxTree.Create($"__v")));
        result.Write(")) (");
        result.Append(valueExpr);
        result.Write(")) ^ \"]\")");
      } else if (t is UserDefinedType { ResolvedClass: TupleTypeDecl tt }) {
        var n = tt.NonGhostDims;
        if (n == 0) {
          result.Write("\"()\"");
        } else {
          var names = Enumerable.Range(0, n).Select(i => $"__t{i}").ToList();
          result.Write("(let ({0}) = (", string.Join(", ", names));
          result.Append(valueExpr);
          result.Write(") in \"(\" ^ ");
          result.Write(string.Join(" ^ \", \" ^ ", names.Zip(t.TypeArgs, (nm, ty) => {
            var s = ExprToString(ty, ConcreteSyntaxTree.Create($"{nm}"));
            return s.ToString();
          })));
          result.Write(" ^ \")\")");
        }
      } else if (t is UserDefinedType { ResolvedClass: TypeParameter parameter }) {
        result.Write("(({0}).DafnyRuntime.TypeDescriptor.to_string (",
          DescriptorName(parameter));
        result.Append(valueExpr);
        result.Write("))");
      } else if (t is UserDefinedType { ResolvedClass: DatatypeDecl dt } datatypeType) {
        result.Write("({0} (", DatatypeToStringFunction(datatypeType, dt));
        result.Append(valueExpr);
        result.Write("))");
      } else if (!t.IsObjectQ && ResolveClassLikeDecl(t) is ClassDecl or TraitDecl) {
        result.Write("(match ");
        result.Append(valueExpr);
        result.Write(" with None -> \"null\" | Some __x -> " +
                     "DafnyRuntime.reference_type_name __x)");
      } else if (t.IsRefType) {
        result.Write("(match ");
        result.Append(valueExpr);
        if (t.IsObjectQ) {
          result.Write(" with None -> \"null\" | Some _ -> \"<object>\")");
        } else {
          result.Write(" with None -> \"null\" | Some __x -> __x.d_dafny_type_name)");
        }
      } else {
        // A bare/erased type parameter or other type we can't recursively format: best effort.
        result.Write("\"<value>\"");
      }
      return result;
    }

    private readonly Dictionary<DatatypeDecl, string> datatypeToStringFunctions = new();

    private string DatatypeToStringFunction(UserDefinedType type, DatatypeDecl dt) {
      if (!datatypeToStringFunctions.TryGetValue(dt, out var rawName)) {
        // This is created lazily, on demand from wherever a value of this datatype first needs to
        // be printed — which may be a *different* module than dt's own. The function conceptually
        // belongs with dt's type declaration, so it must be defined in dt's own file (using dt's
        // raw, unqualified flat name) regardless of who's asking; temporarily switching
        // enclosingModule/currentBlocks makes every FlatName/NewValueDecl call below (including
        // reentrant ones, e.g. via ExprToString on a nested datatype-typed field) resolve exactly
        // as if dt's module were being compiled normally.
        var owningModule = dt.EnclosingModuleDefinition;
        var flatName = RawFlatName(dt);
        rawName = flatName + ModuleSeparator + "d_to_string";
        datatypeToStringFunctions[dt] = rawName;

        var savedModule = enclosingModule;
        var savedBlocks = currentBlocks;
        enclosingModule = owningModule;
        currentBlocks = moduleBlocks[owningModule];
        try {
          var isCo = dt is CoDatatypeDecl;
          var header = rawName;
          foreach (var parameter in dt.TypeArgs) {
            header += " " + DescriptorName(parameter);
          }
          header += " __v";
          var w = NewValueDecl(header);
          w.Write("match {0} with ", isCo ? "(Lazy.force __v)" : "__v");
          var sep = "";
          foreach (var ctor in dt.Ctors) {
            w.Write(sep);
            sep = " | ";
            var nonGhost = ctor.Formals.Where(f => !f.IsGhost).ToList();
            var printableName =
              (dt.EnclosingModuleDefinition.TryToAvoidName
                ? ""
                : dt.EnclosingModuleDefinition.Name + ".") +
              dt.Name + "." + ctor.Name;
            if (isCo || nonGhost.Count == 0) {
              w.Write("{0} -> {1}", CtorPatternWildcard(ctor),
                TargetStringLiteral(printableName));
            } else {
              var names = nonGhost.Select((_, i) => $"__a{i}").ToList();
              var pattern = nonGhost.Count == 1
                  ? $"{CtorName(ctor)} {names[0]}"
                  : $"{CtorName(ctor)} ({string.Join(", ", names)})";
              w.Write("{0} -> {1} ^ \"(\" ^ ", pattern, TargetStringLiteral(printableName));
              w.Write(string.Join(" ^ \", \" ^ ", names.Zip(nonGhost,
                (nm, f) => f.Type.IsStringType
                  ? $"DafnyRuntime.Seq.string_literal_of_chars " +
                    $"{(UnicodeCharEnabled ? "true" : "false")} ({nm})"
                  : ExprToString(f.Type, ConcreteSyntaxTree.Create($"{nm}")).ToString())));
              w.Write(" ^ \")\"");
            }
          }
          w.WriteLine();
        } finally {
          enclosingModule = savedModule;
          currentBlocks = savedBlocks;
        }
      }
      var name = ModuleQualifier(dt.EnclosingModuleDefinition) + rawName;
      if (dt.TypeArgs.Count == 0) {
        return name;
      }
      return "(" + name + " " +
             string.Join(" ", type.TypeArgs.Select(argument =>
               $"({TypeDescriptor(argument, new ConcreteSyntaxTree(), argument.Origin)})")) +
             ")";
    }

    private class ILvalueImpl : ILvalue {
      private readonly OCamlCodeGenerator codeGenerator;
      private readonly Action<ConcreteSyntaxTree> read;
      private readonly Action<ConcreteSyntaxTree, Action<ConcreteSyntaxTree>> write;
      private readonly bool appendTerminator;

      public ILvalueImpl(OCamlCodeGenerator codeGenerator, Action<ConcreteSyntaxTree> read,
        Action<ConcreteSyntaxTree, Action<ConcreteSyntaxTree>> write,
        bool appendTerminator = true) {
        this.codeGenerator = codeGenerator;
        this.read = read;
        this.write = write;
        this.appendTerminator = appendTerminator;
      }

      public void EmitRead(ConcreteSyntaxTree wr) => read(wr);

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        var rhsWriter = new ConcreteSyntaxTree();
        write(wr, w => w.Append(rhsWriter));
        if (appendTerminator) {
          wr.WriteLine(";");
        }
        return rhsWriter;
      }
    }
  }
}
