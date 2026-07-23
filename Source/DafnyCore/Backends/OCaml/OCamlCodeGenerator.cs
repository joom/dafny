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
using JetBrains.Annotations;

namespace Microsoft.Dafny.Compilers {

  // This backend deliberately favors simplicity over completeness and performance. See
  // Docs/Compilation/OCaml.md for the design rationale. In short:
  //   - Every Dafny module, class and datatype is flattened into a single OCaml compilation
  //     unit; there is no attempt to use OCaml's module system to mirror Dafny's module system.
  //     Name clashes are avoided by mangling every top-level name with its enclosing module and
  //     class/datatype name.
  //   - All type declarations across the whole program are threaded together into a single
  //     `type ... and ... and ...` block, and all functions/methods into a single
  //     `let rec ... and ... and ...` block. This sidesteps any need to reorder declarations to
  //     satisfy OCaml's "define before use" rule.
  //   - Every local variable and formal parameter is compiled to an OCaml `ref` cell, read with
  //     `!` and written with `:=`. This is not idiomatic OCaml, but it means the compiler doesn't
  //     need to distinguish mutable from immutable bindings, which keeps it simple.
  //   - Classes compile to mutable records. Every non-static method/function also gets a
  //     closure field (wired to the corresponding top-level function, applied to the record
  //     itself), because the framework compiles every instance call as `receiver.name(args)`,
  //     not just field reads. There's no OCaml analogue of a distinguished `null`, so `null`
  //     compiles to a fresh all-default instance rather than a sentinel; this means `==null`
  //     comparisons aren't reliable (see Docs/Compilation/OCaml.md).
  //   - `int` (and all bit-vector/native numeric types) is Zarith's arbitrary-precision `Z.t`;
  //     `real` is Zarith's `Q.t`; `char` is a plain `int` Unicode code point.
  //   - `seq`/`array` are OCaml arrays; `set` is a deduplicated list; `multiset` is an
  //     (element, multiplicity) list; `map` is an association list. See DafnyRuntime.ml.
  class OCamlCodeGenerator : SinglePassCodeGenerator {

    public OCamlCodeGenerator(DafnyOptions options, ErrorReporter reporter) : base(options, reporter) {
    }

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.Codatatypes,
      Feature.Traits,
      Feature.Iterators,
      Feature.RuntimeTypeDescriptors,
      Feature.MultiDimensionalArrays,
      Feature.CollectionsOfTraits,
      Feature.Quantifiers,
      Feature.NewObject,
      Feature.BitvectorRotateFunctions,
      Feature.NonSequentializableForallStatements,
      Feature.Ordinals,
      Feature.MapItems,
      Feature.LetSuchThatExpressions,
      Feature.TypeTests,
      Feature.SubsetTypeTests,
      Feature.SequenceDisplaysOfCharacters,
      Feature.ExactBoundedPool,
      Feature.RunAllTests,
      Feature.MethodSynthesis,
      Feature.BuiltinsInRuntime,
      Feature.RuntimeCoverageReport,
      Feature.StandardLibraries,
      Feature.StandardLibrariesActionsExterns,
      Feature.ExternalClasses,
      Feature.AllUnderscoreExternalModuleNames,
    };

    public override string ModuleSeparator => "__";
    // Everything is flattened (see the class comment), so "member access" for a static
    // function/method is really just the flat-name separator, not a real qualifier.
    protected override string StaticClassAccessor => ModuleSeparator;
    // Instance calls compile as `receiver.name(args)`, which is why every instance
    // method/function also gets a closure field on the record (see CreateClass/EmitNew).
    protected override string InstanceClassAccessor => ".";
    protected override bool SupportsProperties => false;

    // ----- Buffers that everything gets threaded into ---------------------------------------

    // `exception` declarations, used to compile `break`/`continue` (see CreateLabeledCode).
    private ConcreteSyntaxTree exceptionBlock;
    private readonly HashSet<string> declaredExceptions = [];

    // All `type` declarations (records for classes, variants for datatypes), joined with `and`.
    private ConcreteSyntaxTree typeBlock;
    private bool anyTypeDeclared;

    // All top-level function/method bodies, joined with `and` under a single `let rec`.
    private ConcreteSyntaxTree valueBlock;
    private bool anyValueDeclared;

    private void DeclareExceptionOnce(string name) {
      if (declaredExceptions.Add(name)) {
        exceptionBlock.WriteLine("exception {0}", name);
      }
    }

    private ConcreteSyntaxTree NewTypeDecl(string header) {
      typeBlock.Write(anyTypeDeclared ? "and " : "type ");
      anyTypeDeclared = true;
      typeBlock.Write(header);
      var w = typeBlock.Fork(1);
      typeBlock.WriteLine();
      return w;
    }

    private ConcreteSyntaxTree NewValueDecl(string header) {
      valueBlock.Write(anyValueDeclared ? "and " : "let rec ");
      anyValueDeclared = true;
      valueBlock.Write(header);
      valueBlock.Write(" =");
      var w = valueBlock.Fork(1);
      valueBlock.WriteLine();
      return w;
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("(* Dafny program {0} compiled into OCaml *)", program.Name);
      if (Options.IncludeRuntime) {
        EmitRuntimeSource("DafnyRuntimeOCaml", wr);
      }
      exceptionBlock = wr.Fork();
      typeBlock = wr.Fork();
      valueBlock = wr.Fork();
    }

    protected override void EmitFooter(Program program, ConcreteSyntaxTree wr) {
      if (!anyTypeDeclared) {
        // Keep the `and`-chain machinery simple by always having at least one dummy type.
        typeBlock.WriteLine("type __dafny_unused_placeholder__ = unit");
      }
      if (!anyValueDeclared) {
        valueBlock.WriteLine("let rec __dafny_unused_placeholder__ () = ()");
      }
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      var companion = TypeName_Companion(UserDefinedType.FromTopLevelDecl(mainMethod.Origin, mainMethod.EnclosingClass), wr, mainMethod.Origin, mainMethod);
      wr.WriteLine("let () =");
      var body = wr.Fork(1);
      body.WriteLine("try {0}{1}{2} ()", companion, ModuleSeparator, IdName(mainMethod));
      body.WriteLine("with DafnyRuntime.Halt msg -> Printf.eprintf \"%s\\n\" (\"Program halted: \" ^ msg); exit 1");
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      var w = (cw as ClassWriter).ValueWriter;
      return NewValueDecl($"{(cw as ClassWriter).FlatName}{ModuleSeparator}Main ({argsParameterName})");
    }

    protected override ConcreteSyntaxTree CreateModule(ModuleDefinition module, string moduleName, bool isDefault,
      ModuleDefinition externModule,
      string libraryName /*?*/, Attributes moduleAttributes, ConcreteSyntaxTree wr) {
      // Modules are flattened away; see the class comment. Every declaration inside the module
      // gets its full name (including this module's name) via FlatName/FullTypeName.
      return wr;
    }

    protected override string GetHelperModuleName() => "DafnyRuntime";

    // ----- Naming -----------------------------------------------------------------------------

    private static string LowerFirst(string s) {
      if (s.Length == 0 || char.IsLower(s[0]) || s[0] == '_') {
        return s;
      }
      return char.ToLowerInvariant(s[0]) + s.Substring(1);
    }

    private static string UpperFirst(string s) {
      if (s.Length == 0 || char.IsUpper(s[0])) {
        return s;
      }
      if (s[0] == '_') {
        return "Ctor" + s;
      }
      return char.ToUpperInvariant(s[0]) + s.Substring(1);
    }

    // The flattened, globally-unique name of a class/datatype/newtype: "<module>__<decl>".
    private string FlatName(TopLevelDecl d) {
      var modName = d.EnclosingModuleDefinition.GetCompileName(Options);
      return IdProtect(LowerFirst(modName) + "__" + d.GetCompileName(Options));
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
        ValueWriter = codeGenerator.valueBlock;
      }

      public ConcreteSyntaxTree CreateMethod(MethodOrConstructor m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return CodeGenerator.CreateSubroutine(FlatName, CodeGenerator.IdName(m), m.Ins, m.Outs, m.IsStatic, createBody, false);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(m.Origin, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
        List<Formal> formals, Type resultType, IOrigin tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return CodeGenerator.CreateSubroutine(FlatName, name, formals, [], isStatic, createBody, true);
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IOrigin tok, bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        return CodeGenerator.CreateSubroutine(FlatName, name, [], [], isStatic, createBody, true);
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IOrigin tok, bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        setterWriter = createBody ? CodeGenerator.CreateSubroutine(FlatName, name + "__set", [], [], false, true, false) : null;
        return createBody ? CodeGenerator.CreateSubroutine(FlatName, name, [], [], false, true, true) : null;
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IOrigin tok, string rhs, Field field) {
        CodeGenerator.DeclareField(FlatName, name, isStatic, type, tok, rhs, FieldWriter, ValueWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new Cce.UnreachableException();
      }

      public ConcreteSyntaxTree ErrorWriter() => ValueWriter;
      public void Finish() { }
    }


    protected void DeclareField(string flatClassName, string name, bool isStatic, Type type, IOrigin tok, string rhs,
        ConcreteSyntaxTree fieldWriter, ConcreteSyntaxTree wr) {
      var value = rhs ?? DefaultValue(type, wr, tok);
      if (isStatic) {
        var w = NewValueDecl($"{flatClassName}{ModuleSeparator}{name} : {TypeName(type, wr, tok)} ref");
        w.Write("ref ({0})", value);
      } else {
        fieldWriter.WriteLine("mutable {0}{1}{2} : {3};", flatClassName, ModuleSeparator, name, TypeName(type, fieldWriter, tok));
      }
    }

    private ConcreteSyntaxTree CreateSubroutine(string flatClassName, string name, List<Formal> ins, List<Formal> outs, bool isStatic, bool createBody, bool isFunction) {
      if (!createBody) {
        return null;
      }
      var header = $"{flatClassName}{ModuleSeparator}{name}";
      if (!isStatic) {
        header += " this";
      }
      header += " " + FormalsPattern(ins);
      var w = NewValueDecl(header);
      var body = w.NewBlock("begin", "end", BlockStyle.Newline, BlockStyle.Newline);
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
        // `try` to have type unit).
        tryBlock.WriteLine("assert false");
      } else if (outs.Count > 0) {
        EmitReturn(outs, tryBlock);
      } else {
        tryBlock.WriteLine("()");
      }
      return beforeReturn;
    }

    private string FormalsPattern(List<Formal> formals) {
      var names = formals.Where(f => !f.IsGhost).Select(IdName).ToList();
      if (names.Count == 0) {
        return "()";
      } else if (names.Count == 1) {
        return names[0];
      } else {
        return "(" + string.Join(", ", names) + ")";
      }
    }

    protected override IClassWriter CreateClass(string moduleName, bool isExtern, string fullPrintName,
        List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      if (isExtern) {
        throw new UnsupportedFeatureException(tok, Feature.ExternalClasses);
      }
      if (superClasses != null && superClasses.Any(trait => !trait.IsObject)) {
        throw new UnsupportedFeatureException(tok, Feature.Traits);
      }
      var flatName = FlatName(cls);
      var typeParams = TypeParamString(typeParameters);
      var header = $"{typeParams}{flatName}_t";
      var fieldWriter = NewTypeDecl(header + " = {");
      fieldWriter.WriteLine("mutable {0}__dummy : unit;", flatName); // guarantees the record is non-empty
      // Every non-static method/function gets a closure field too (see EmitNew), so that a call
      // written as `receiver.name(args)` — which is how the framework compiles every instance
      // call, not just field access — resolves to a plain (and thus OCaml-native) field read.
      // Field names here are intentionally NOT flat-name-prefixed, since that's the bare name
      // the framework writes at call sites; OCaml's type-directed disambiguation resolves the
      // ambiguity with same-named fields on unrelated record types.
      foreach (var m in InstanceCallableMembers((TopLevelDeclWithMembers)cls)) {
        fieldWriter.WriteLine("{0} : {1};", IdName(m), MemberClosureFieldType(m, fieldWriter));
      }
      typeBlock.Write("}");
      typeBlock.WriteLine();
      return new ClassWriter(flatName, this, fieldWriter);
    }

    private IEnumerable<MemberDecl> InstanceCallableMembers(TopLevelDeclWithMembers cls) {
      return cls.Members.Where(m => !m.IsGhost && !m.IsStatic && (m is Function || m is MethodOrConstructor));
    }

    private List<Formal> MemberIns(MemberDecl m) => ((MethodOrFunction)m).Ins;

    private string MemberResultTypeString(MemberDecl m, ConcreteSyntaxTree wr) {
      if (m is Function f) {
        return TypeName(f.ResultType, wr, f.Origin);
      }
      var outs = ((MethodOrConstructor)m).Outs.Where(o => !o.IsGhost).ToList();
      if (outs.Count == 0) {
        return "unit";
      } else if (outs.Count == 1) {
        return TypeName(outs[0].Type, wr, outs[0].Origin);
      }
      return "(" + string.Join(" * ", outs.Select(o => TypeName(o.Type, wr, o.Origin))) + ")";
    }

    private string MemberClosureFieldType(MemberDecl m, ConcreteSyntaxTree wr) {
      var ins = MemberIns(m).Where(f => !f.IsGhost).ToList();
      string argType = ins.Count == 0 ? "unit"
        : ins.Count == 1 ? TypeName(ins[0].Type, wr, ins[0].Origin)
        : "(" + string.Join(" * ", ins.Select(f => TypeName(f.Type, wr, f.Origin))) + ")";
      return $"{argType} -> {MemberResultTypeString(m, wr)}";
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TraitDecl trait, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.Traits);
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(iter.Origin, Feature.Iterators);
    }

    private string TypeParamString(List<TypeParameter> typeParameters) {
      if (typeParameters == null || typeParameters.Count == 0) {
        return "";
      }
      return "(" + string.Join(", ", typeParameters.Select(tp => "'" + LowerFirst(IdName(tp)))) + ") ";
    }

    // ----- Datatypes ----------------------------------------------------------------------------

    protected override bool DatatypeDeclarationAndMemberCompilationAreSeparate => true;
    public override bool SupportsDatatypeWrapperErasure => false;

    private string CtorName(DatatypeCtor ctor) => UpperFirst(IdProtect(ctor.GetCompileName(Options)));

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      if (dt is TupleTypeDecl) {
        return null; // Dafny tuples are OCaml tuples; no declaration needed.
      }

      var flatName = FlatName(dt);
      var typeParams = TypeParamString(dt.TypeArgs);
      var header = $"{typeParams}{flatName}_t =";
      var w = NewTypeDecl(header);
      foreach (var ctor in dt.Ctors) {
        w.Write("\n| {0}", CtorName(ctor));
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
        var witness = new ConcreteSyntaxTree();
        var wStmts = new ConcreteSyntaxTree();
        witness.Append(Expr(nt.Witness, false, wStmts));
        DeclareField(flatName, "Witness", true, nt.BaseType, nt.Origin, witness.ToString(), null, wr);
      }
      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var flatName = FlatName(sst);
        var witness = new ConcreteSyntaxTree();
        witness.Append(Expr(sst.Witness, false, wr));
        DeclareField(flatName, "Witness", true, sst.Rhs, sst.Origin, witness.ToString(), null, wr);
      }
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
      needsTypeDescriptor = false;
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      throw new UnsupportedFeatureException(tok, Feature.RuntimeTypeDescriptors);
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl member = null) {
      Contract.Assume(type != null);
      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        return "'_dafny_unknown";
      } else if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return "int";
      } else if (xType is IntType or BigOrdinalType) {
        return "DafnyRuntime.Int.t";
      } else if (xType is RealType) {
        return "Q.t";
      } else if (xType is BitvectorType) {
        return "DafnyRuntime.Int.t";
      } else if (xType.AsNewtype is { } newtypeDecl) {
        return TypeName(newtypeDecl.ConcreteBaseType(xType.TypeArgs), wr, tok, member);
      } else if (xType.IsObjectQ) {
        return "unit"; // `new object()` is unsupported (Feature.NewObject); this is just a placeholder
      } else if (xType.IsArrayType) {
        var at = xType.AsArrayType;
        if (at.Dims != 1) {
          throw new UnsupportedFeatureException(tok, Feature.MultiDimensionalArrays);
        }
        var elType = UserDefinedType.ArrayElementType(xType);
        return TypeName(elType, wr, tok) + " array";
      } else if (xType is UserDefinedType udt) {
        return TypeName_UDT(FullTypeName(udt, member), udt, wr, tok);
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
      var xType = type.NormalizeExpand();
      if (xType is UserDefinedType udt && udt.ResolvedClass != null) {
        return FlatName(udt.ResolvedClass);
      }
      return TypeName(type, wr, tok, member);
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      Contract.Assume(udt != null);
      if (udt is ArrowType) {
        return "arrow";
      }
      var cl = udt.ResolvedClass;
      if (cl is TypeParameter tp) {
        return "'" + LowerFirst(IdName(tp));
      }
      if (cl is TupleTypeDecl) {
        return ""; // handled specially: tuples don't need a type name suffix
      }
      return FlatName(cl) + "_t";
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IOrigin tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "0";
      } else if (xType is IntType or BigOrdinalType or BitvectorType) {
        return "DafnyRuntime.Int.zero";
      } else if (xType is RealType) {
        return "Q.zero";
      } else if (xType is SetType) {
        return "[]";
      } else if (xType is MultiSetType) {
        return "[]";
      } else if (xType is SeqType) {
        return "[||]";
      } else if (xType is MapType) {
        return "[]";
      }

      var udt = (UserDefinedType)xType;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TypeParameter or AbstractTypeDecl) {
        return "Obj.magic 0"; // erased type parameter; only reachable for placeholder/ghost purposes
      } else if (cl is NewtypeDecl ntd) {
        if (ntd.Witness != null) {
          return $"!({FlatName(ntd)}{ModuleSeparator}Witness)";
        }
        return TypeInitializationValue(ntd.ConcreteBaseType(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
      } else if (cl is SubsetTypeDecl std) {
        if (std.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          return $"!({FlatName(std)}{ModuleSeparator}Witness)";
        } else if (std.WitnessKind == SubsetTypeDecl.WKind.Special) {
          if (ArrowType.IsPartialArrowTypeName(std.Name) || ArrowType.IsTotalArrowTypeName(std.Name)) {
            var rangeDefault = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
            return $"(fun _ -> {rangeDefault})";
          } else if (((NonNullTypeDecl)std).Class is ArrayClassDecl) {
            return "[||]";
          } else {
            return BuildClassInstance((TopLevelDeclWithMembers)((NonNullTypeDecl)std).Class, wr).ToString();
          }
        } else {
          return TypeInitializationValue(std.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is ArrayClassDecl) {
        return "[||]";
      } else if (cl is ClassLikeDecl) {
        return BuildClassInstance((TopLevelDeclWithMembers)cl, wr).ToString();
      } else if (cl is DatatypeDecl dt) {
        if (dt is TupleTypeDecl ttd) {
          if (ttd.NonGhostDims == 0) {
            return "()";
          }
          return "(" + string.Join(", ", udt.TypeArgs.Select(t => TypeInitializationValue(t, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors))) + ")";
        }
        var groundingCtor = dt.GetGroundingCtor();
        var nonGhost = groundingCtor.Formals.Where(f => !f.IsGhost).ToList();
        if (nonGhost.Count == 0) {
          return CtorName(groundingCtor);
        }
        return $"{CtorName(groundingCtor)} ({string.Join(", ", nonGhost.Select(f => TypeInitializationValue(f.Type, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors)))})";
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();
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

    protected override void DeclareLocalVar(string name, Type type, IOrigin tok, bool leaveRoomForRhs, string rhs, ConcreteSyntaxTree wr) {
      wr.Write("let {0} = ref (", name);
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);
        wr.Write(type != null ? DefaultValue(type, wr, tok) : "Obj.magic 0");
      } else {
        wr.Write(rhs ?? (type != null ? DefaultValue(type, wr, tok) : "Obj.magic 0"));
      }
      wr.WriteLine(") in");
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IOrigin tok, ConcreteSyntaxTree wr) {
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
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitCallReturnOuts(List<string> outTmps, ConcreteSyntaxTree wr) {
      wr.Write("{0} := ", Util.Comma(outTmps));
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
    protected override string AssignmentSymbol => " := ";

    protected override (ConcreteSyntaxTree wArray, ConcreteSyntaxTree wRhs) EmitArrayUpdate(List<Action<ConcreteSyntaxTree>> indices, Type elementType, ConcreteSyntaxTree wr) {
      var wArray = EmitArraySelect(indices, elementType, wr);
      wr.Write(" <- ");
      var wRhs = wr.Fork();
      return (wArray, wRhs);
    }

    protected override void EmitNull(Type type, ConcreteSyntaxTree wr) {
      // There's no analogue of `null` for an OCaml record, so `null` is compiled to a fresh
      // all-default instance of the class instead of a distinguished sentinel value. This means
      // `x == null` isn't reliable (it compares by physical identity, and this never aliases a
      // real `new`-allocated object, nor a previous `null` — see Docs/Compilation/OCaml.md).
      wr.Append(BuildClassInstance(ResolveClassLikeDecl(type), wr));
    }

    private TopLevelDeclWithMembers ResolveClassLikeDecl(Type type) {
      var cl = (type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
      if (cl is NonNullTypeDecl nnd) {
        cl = nnd.Class;
      }
      return cl as TopLevelDeclWithMembers;
    }

    // Builds `let rec this = { <data fields at their defaults>; <method fields, each wired to
    // call the corresponding top-level function with `this` as the receiver> } in this`.
    private ConcreteSyntaxTree BuildClassInstance(TopLevelDeclWithMembers cl, ConcreteSyntaxTree wr) {
      var flatName = FlatName(cl);
      var result = new ConcreteSyntaxTree();
      result.Write("(let rec this = {{ {0}__dummy = ()", flatName);
      foreach (var f in cl.Members.OfType<Field>().Where(fld => !fld.IsStatic && !fld.IsGhost)) {
        result.Write("; {0}{1}{2} = {3}", flatName, ModuleSeparator, IdName(f), DefaultValue(f.Type, wr, f.Origin));
      }
      foreach (var m in InstanceCallableMembers(cl)) {
        var pattern = FormalsPattern(MemberIns(m));
        result.Write("; {0} = (fun {1} -> {2}{3}{4} this {1})", IdName(m), pattern, flatName, ModuleSeparator, IdName(m));
      }
      result.Write(" } in this)");
      return result;
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
      wr.Append(ExprToString(arg.Type, Expr(arg, false, wStmts)));
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
      wr.WriteLine("DafnyRuntime.halt \"{0}\";", message ?? "unexpected control point");
    }

    protected override void EmitHalt(IOrigin tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("DafnyRuntime.halt (");
      if (tok != null) {
        wr.Write("\"" + TranslateEscapes(tok.OriginToString(Options)) + ": \" ^ ");
      }
      wr.Append(ExprToString(messageExpr.Type, Expr(messageExpr, false, wStmts)));
      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IOrigin tok, IVariable loopIndex, bool goingUp,
      string endVarName, List<Statement> body, List<Label> labels, ConcreteSyntaxTree wr) {
      var indexName = IdName(loopIndex);
      wr.Write("let {0} = ref (", indexName);
      var startWriter = wr.Fork();
      wr.WriteLine(") in");
      var cond = endVarName == null ? "true" : goingUp ? $"!{indexName} < !{endVarName}" : $"!{indexName} > !{endVarName}";
      DeclareExceptionOnce("Dafny_break_loop");
      wr.Write("(try ");
      var w = wr.NewNamedBlock("while ({0}) do", cond);
      w = EmitContinueLabel(labels, w);
      Coverage.Instrument(tok, "for loop body", w);
      TrStmtList(body, w);
      w.WriteLine(goingUp ? "{0} := DafnyRuntime.Int.succ !{0};" : "{0} := DafnyRuntime.Int.pred !{0};", indexName);
      wr.WriteLine("done with Dafny_break_loop -> ());");
      return startWriter;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, Action<ConcreteSyntaxTree> bound, ConcreteSyntaxTree wr, string start = null) {
      wr.Write("let {0} = ref ({1}) in", indexVar, start ?? "0");
      wr.WriteLine();
      wr.Write("while (!{0} < (", indexVar);
      bound(wr);
      var wBody = wr.NewBlock(")) do", "done;", BlockStyle.Newline, BlockStyle.Newline);
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

    protected override string GetQuantifierName(string bvType) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Quantifiers);
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IOrigin tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      wr.Write("Array.iter (fun {0} -> let {0} = ref {0} in ", tmpVarName);
      collectionWriter = wr.Fork();
      var body = wr.NewBlock(")", ";", BlockStyle.Newline, BlockStyle.Newline);
      body.Fork(0).WriteLine("();");
      return body;
    }

    [CanBeNull]
    protected override Action<ConcreteSyntaxTree> GetSubtypeCondition(string tmpVarName, Type boundVarType, IOrigin tok, ConcreteSyntaxTree wPreconditions) {
      return null;
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type sourceType, bool introduceBoundVar, IOrigin tok, ConcreteSyntaxTree wr) {
      if (introduceBoundVar) {
        wr.WriteLine("let {0} = ref {1} in", boundVarName, tmpVarName);
      } else {
        wr.WriteLine("{0} := {1};", boundVarName, tmpVarName);
      }
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      wr.Write("Array.iter (fun {0} -> ", boundVarName);
      collectionWriter = wr.Fork();
      return wr.NewBlock(")", ";", BlockStyle.Newline, BlockStyle.Newline);
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, IOrigin tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      // Allocate the record with every field at its type's default value; the actual Dafny
      // constructor (if any) then runs as an ordinary method call right after (see how
      // SinglePassCodeGenerator.cs uses allocateClass.InitCall), mutating fields as needed.
      wr.Append(BuildClassInstance(ResolveClassLikeDecl(type), wr));
    }

    protected override void EmitNewArray(Type elementType, IOrigin tok, List<string> dimensions,
        bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (dimensions.Count != 1) {
        throw new UnsupportedFeatureException(tok, Feature.MultiDimensionalArrays);
      }
      var initValue = exampleElement ?? DefaultValue(elementType, wr, tok);
      wr.Write("(Array.make (DafnyRuntime.Int.to_int ({0})) ({1}))", dimensions[0], initValue);
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
        wr.Write("(DafnyRuntime.Seq.of_string (");
        TrStringLiteral(str, wr);
        wr.Write("))");
      } else if (e.Value is BigInteger i) {
        wr.Write("(DafnyRuntime.Int.of_string \"{0}\")", i);
      } else if (e.Value is BaseTypes.BigDec d) {
        wr.Write("(Q.of_string \"{0}\")", d.ToDecimalString());
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();
      }
    }

    private static string TranslateEscapes(string s) => Util.ReplaceNullEscapesWithCharacterEscapes(s);

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      // Non-verbatim Dafny string literals already carry their escape sequences (\n, \t, \\, ...)
      // as literal two-character sequences in `str`, in the same syntax OCaml uses, so (as with
      // the C++ backend) the common case is just to pass them through unchanged.
      if (!isVerbatim) {
        wr.Write("\"{0}\"", TranslateEscapes(str));
        return;
      }
      var n = str.Length;
      wr.Write("\"");
      for (var i = 0; i < n; i++) {
        if (str[i] == '\"' && i + 1 < n && str[i + 1] == '\"') {
          wr.Write("\\\"");
          i++;
        } else if (str[i] == '\\') {
          wr.Write("\\\\");
        } else if (str[i] == '\n') {
          wr.Write("\\n");
        } else if (str[i] == '\r') {
          wr.Write("\\r");
        } else {
          wr.Write(str[i]);
        }
      }
      wr.Write("\"");
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, [CanBeNull] NativeType nativeType,
      bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      wr.Write("(DafnyRuntime.Int.truncate {0} false (", bvType.Width);
      var middle = wr.Fork();
      wr.Write("))");
      return middle;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
      bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      throw new UnsupportedFeatureException(e0.Origin, Feature.BitvectorRotateFunctions);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override string IdProtect(string name) => PublicIdProtect(name);

    private static readonly HashSet<string> OCamlKeywords = new() {
      "and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done", "downto", "else",
      "end", "exception", "external", "false", "for", "fun", "function", "functor", "if", "in",
      "include", "inherit", "initializer", "land", "lazy", "let", "lor", "lsl", "lsr", "lxor",
      "match", "method", "mod", "module", "mutable", "new", "nonrec", "object", "of", "open", "or",
      "private", "rec", "sig", "struct", "then", "to", "true", "try", "type", "val", "virtual",
      "when", "while", "with", "asr", "land", "this", "ref",
    };

    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      if (name.Length == 0) {
        return name;
      }
      var n = LowerFirst(name);
      if (OCamlKeywords.Contains(n)) {
        return n + "_";
      }
      return n;
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember) {
      wr.Write("this");
    }

    private static readonly System.Text.RegularExpressions.Regex BareIdentifier =
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

    protected override void EmitDatatypeValue(DatatypeValue dtv, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      if (dt is TupleTypeDecl) {
        wr.Write(arguments.Length == 0 ? "()" : "({0})", arguments);
      } else {
        var ctorName = CtorName(dtv.Ctor);
        wr.Write(arguments.Length == 0 ? ctorName : "({0} ({1}))", ctorName, arguments);
      }
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
          compiledName = "";
          break;
        case SpecialField.ID.Floor:
          compiledName = "";
          break;
        case SpecialField.ID.Keys:
          compiledName = "";
          break;
        case SpecialField.ID.Values:
          compiledName = "";
          break;
        case SpecialField.ID.Items:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.MapItems);
        case SpecialField.ID.Reads:
        case SpecialField.ID.Modifies:
        case SpecialField.ID.New:
          compiledName = "";
          break;
        case SpecialField.ID.IsLimit:
        case SpecialField.ID.IsSucc:
        case SpecialField.ID.Offset:
        case SpecialField.ID.IsNat:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.Ordinals);
        default:
          Contract.Assert(false);
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
      Type expectedType, string additionalCustomParameter = null, bool internalAccess = false) {
      if (member is DatatypeDestructor dtor && dtor.EnclosingClass is TupleTypeDecl ttd) {
        var idx = ttd.NonGhostDims == 1 ? 0 : ttd.Ctors[0].Formals.IndexOf(dtor.CorrespondingFormals[0]);
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
        return SimpleLvalue(wr => {
          wr.Write("(match ");
          obj(wr);
          wr.Write(" with {0} -> true | _ -> false)", CtorPatternWildcard(FindCtor(disc)));
        });
      } else if (member is SpecialField sf && sf.SpecialId == SpecialField.ID.ArrayLength) {
        return SimpleLvalue(wr => {
          wr.Write("(DafnyRuntime.Seq.length (");
          obj(wr);
          wr.Write("))");
        });
      } else if (member is SpecialField sf2 && sf2 is DatatypeDestructor dtor2) {
        var ctor = dtor2.EnclosingCtors[0];
        return SimpleLvalue(wr => {
          wr.Write("(match ");
          obj(wr);
          wr.Write(" with {0} -> {1}", DestructorPattern(dtor2, out var varName), varName);
          wr.Write(" | _ -> DafnyRuntime.halt \"unexpected constructor\")");
        });
      } else if (member is SpecialField sf3) {
        GetSpecialFieldInfo(sf3.SpecialId, sf3.IdParam, objType, out var compiledName, out _, out _);
        if (compiledName == "") {
          return SimpleLvalue(obj);
        }
        return SuffixLvalue(obj, ".{0}", compiledName);
      } else if (member is Field f && !member.IsStatic) {
        var cl = member.EnclosingClass;
        var fieldName = FlatName(cl) + ModuleSeparator + IdName(member);
        return new ILvalueImpl(this, wr => {
          obj(wr);
          wr.Write(".{0}", fieldName);
        }, (wr, rhs) => {
          obj(wr);
          wr.Write(".{0} <- (", fieldName);
          rhs(wr);
          wr.Write(")");
        });
      } else if (member.IsStatic) {
        var companion = TypeName_Companion(objType, null, member.Origin, member);
        var flatMemberName = $"{companion}{ModuleSeparator}{IdName(member)}";
        if (member is Field) {
          return SimpleLvalue(wr => wr.Write("!({0})", flatMemberName));
        }
        return SimpleLvalue(wr => wr.Write(flatMemberName));
      } else {
        // A non-static function/method being referenced/torn off as a value: every class
        // instance carries a closure field per instance member (see CreateClass/EmitNew), so
        // this is just an ordinary field read.
        return SimpleLvalue(wr => {
          obj(wr);
          wr.Write(".{0}", IdName(member));
        });
      }
    }

    private DatatypeCtor FindCtor(DatatypeDiscriminator disc) {
      return disc.EnclosingClass is DatatypeDecl dt ? dt.Ctors.First(c => c.Name == disc.IdParam.ToString()) : null;
    }

    private string CtorPatternWildcard(DatatypeCtor ctor) {
      if (ctor == null) {
        return "_";
      }
      var nonGhost = ctor.Formals.Count(f => !f.IsGhost);
      return nonGhost == 0 ? CtorName(ctor) : $"{CtorName(ctor)} _";
    }

    private string DestructorPattern(DatatypeDestructor dtor, out string varName) {
      varName = "__x";
      var ctor = dtor.EnclosingCtors[0];
      var nonGhost = ctor.Formals.Where(f => !f.IsGhost).ToList();
      var idx = nonGhost.FindIndex(f => f == dtor.CorrespondingFormals[0]);
      if (nonGhost.Count == 1) {
        return CtorName(ctor) + " " + varName;
      }
      var vn = varName;
      return CtorName(ctor) + " (" + string.Join(", ", nonGhost.Select((_, i) => i == idx ? vn : "_")) + ")";
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Action<ConcreteSyntaxTree>> indices, Type elmtType, ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      Contract.Assert(indices.Count == 1);
      wr.Write(".(DafnyRuntime.Int.to_int (");
      indices[0](wr);
      wr.Write("))");
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices.Count == 1);
      var w = wr.Fork();
      wr.Write(".(DafnyRuntime.Int.to_int (");
      wr.Append(Expr(indices[0], inLetExprBody, wStmts));
      wr.Write("))");
      return w;
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(DafnyRuntime.Int.to_int (");
      wr.Append(Expr(expr, inLetExprBody, wStmts));
      wr.Write("))");
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (source.Type.NormalizeToAncestorType() is MapType) {
        wr.Write("(DafnyRuntime.Map_.get ((");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (source.Type.NormalizeToAncestorType() is MultiSetType) {
        wr.Write("(DafnyRuntime.Multiset.multiplicity (");
        wr.Append(Expr(index, inLetExprBody, wStmts));
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
        wr.Write("(DafnyRuntime.Map_.update ((");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(CoercedExpr(value, resultCollectionType.ValueArg, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (resultCollectionType is MultiSetType) {
        wr.Write("(DafnyRuntime.Multiset.update ((");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(CoercedExpr(value, resultCollectionType.ValueArg, inLetExprBody, wStmts));
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

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi,
        bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (lo == null && hi == null) {
        wr.Write("(Array.copy (");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write("))");
      } else if (lo == null) {
        wr.Write("(DafnyRuntime.Seq.take ((");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(hi, inLetExprBody, wStmts));
        wr.Write(")))");
      } else if (hi == null) {
        wr.Write("(DafnyRuntime.Seq.drop ((");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write("), (");
        wr.Append(Expr(lo, inLetExprBody, wStmts));
        wr.Write(")))");
      } else {
        wr.Write("(DafnyRuntime.Seq.sub ((");
        wr.Append(Expr(source, inLetExprBody, wStmts));
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
      wr.Write(") (fun __i -> (");
      wr.Append(CoercedExpr(expr.Initializer, expr.Type.NormalizeToAncestorType().AsSeqType.Arg, inLetExprBody, wStmts));
      wr.Write(") __i))");
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      var fromType = expr.E.Type.NormalizeToAncestorType();
      wr.Write(fromType is SetType ? "(DafnyRuntime.Multiset.of_set (" : "(DafnyRuntime.Multiset.of_seq (");
      wr.Append(Expr(expr.E, inLetExprBody, wStmts));
      wr.Write("))");
    }

    protected override void EmitApplyExpr(Type functionType, IOrigin tok, Expression function, List<Expression> arguments,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(");
      wr.Append(Expr(function, inLetExprBody, wStmts));
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IOrigin tok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      wr.Write("((fun {0} -> ", boundVars.Count == 0 ? "()" : boundVars.Count == 1 ? boundVars[0] : "(" + string.Join(", ", boundVars) + ")");
      var w = wr.Fork();
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      wr.Write(")");
      return w;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      wr.Write("(match !{0} with {1} -> true | _ -> false)", source, CtorPatternWildcard(ctor));
    }

    protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex,
      DatatypeCtor ctor, Func<List<Type>> getTypeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (ctor.EnclosingDatatype is TupleTypeDecl ttd) {
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
      source(wr);
      wr.Write(" with {0} -> __x | _ -> DafnyRuntime.halt \"unexpected constructor\")", pattern);
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IOrigin tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      var pat = inNames.Count == 0 ? "()" : inNames.Count == 1 ? inNames[0] : "(" + string.Join(", ", inNames) + ")";
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
      wr.Write("(let {0} = (", bvName);
      wrRhs = wr.Fork();
      wr.Write(") in ");
      wStmts = wr.Fork();
      wrBody = wr.Fork();
      wr.Write(")");
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IOrigin resultTok, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("((fun () -> ");
      var w = wr.Fork();
      wr.Write(") ())");
      return w;
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IOrigin resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(resultTok, Feature.LetSuchThatExpressions);
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

    bool IsDirectlyComparable(Type t) => t.IsBoolType || t.IsCharType;

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

      var isNumeric = e0Type.NormalizeToAncestorType().IsNumericBased() || e0Type.NormalizeToAncestorType().IsBitVectorType;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff: opString = "="; break;
        case BinaryExpr.ResolvedOpcode.Imp: preOpString = "not"; opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.Or: opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.And: opString = "&&"; break;

        case BinaryExpr.ResolvedOpcode.BitwiseAnd: staticCallString = "DafnyRuntime.Int.logand"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr: staticCallString = "DafnyRuntime.Int.logor"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor: staticCallString = "DafnyRuntime.Int.logxor"; break;

        case BinaryExpr.ResolvedOpcode.EqCommon:
          opString = e0Type.NormalizeToAncestorType().IsRefType ? "==" : "=";
          break;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          opString = e0Type.NormalizeToAncestorType().IsRefType ? "!=" : "<>";
          break;

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<"; break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<="; break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">="; break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">"; break;

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
            staticCallString = "DafnyRuntime.Int.add_char";
          } else if (resultType.NormalizeToAncestorType() is RealType) {
            staticCallString = "Q.add";
          } else {
            staticCallString = "DafnyRuntime.Int.add";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          truncateResult = true;
          if (resultType.IsCharType) {
            staticCallString = "DafnyRuntime.Int.sub_char";
          } else if (resultType.NormalizeToAncestorType() is RealType) {
            staticCallString = "Q.sub";
          } else {
            staticCallString = "DafnyRuntime.Int.sub";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          truncateResult = true;
          staticCallString = resultType.NormalizeToAncestorType() is RealType ? "Q.mul" : "DafnyRuntime.Int.mul";
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          staticCallString = resultType.NormalizeToAncestorType() is RealType ? "Q.div" : "DafnyRuntime.Int.ediv";
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          staticCallString = "DafnyRuntime.Int.erem";
          break;

        case BinaryExpr.ResolvedOpcode.SetEq: staticCallString = "DafnyRuntime.Set.equal"; break;
        case BinaryExpr.ResolvedOpcode.MultiSetEq: staticCallString = "DafnyRuntime.Multiset.equal"; break;
        case BinaryExpr.ResolvedOpcode.MapEq: staticCallString = "DafnyRuntime.Map_.equal"; break;
        case BinaryExpr.ResolvedOpcode.SeqEq: opString = "="; break;
        case BinaryExpr.ResolvedOpcode.SetNeq: preOpString = "not"; staticCallString = "DafnyRuntime.Set.equal"; break;
        case BinaryExpr.ResolvedOpcode.MultiSetNeq: preOpString = "not"; staticCallString = "DafnyRuntime.Multiset.equal"; break;
        case BinaryExpr.ResolvedOpcode.MapNeq: preOpString = "not"; staticCallString = "DafnyRuntime.Map_.equal"; break;
        case BinaryExpr.ResolvedOpcode.SeqNeq: opString = "<>"; break;

        case BinaryExpr.ResolvedOpcode.ProperSubset: staticCallString = "DafnyRuntime.Set.is_proper_subset"; break;
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset: staticCallString = "DafnyRuntime.Multiset.is_proper_subset"; break;
        case BinaryExpr.ResolvedOpcode.Subset: staticCallString = "DafnyRuntime.Set.is_subset"; break;
        case BinaryExpr.ResolvedOpcode.MultiSubset: staticCallString = "DafnyRuntime.Multiset.is_subset"; break;
        case BinaryExpr.ResolvedOpcode.Superset: staticCallString = "DafnyRuntime.Set.is_subset"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.MultiSuperset: staticCallString = "DafnyRuntime.Multiset.is_subset"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.ProperSuperset: staticCallString = "DafnyRuntime.Set.is_proper_subset"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset: staticCallString = "DafnyRuntime.Multiset.is_proper_subset"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Disjoint: staticCallString = "DafnyRuntime.Set.is_disjoint"; break;
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint: staticCallString = "DafnyRuntime.Multiset.is_disjoint"; break;

        case BinaryExpr.ResolvedOpcode.InSet: staticCallString = "DafnyRuntime.Set.mem"; break;
        case BinaryExpr.ResolvedOpcode.InMultiSet: staticCallString = "DafnyRuntime.Multiset.mem"; break;
        case BinaryExpr.ResolvedOpcode.InMap: staticCallString = "DafnyRuntime.Map_.has_key"; break;
        case BinaryExpr.ResolvedOpcode.NotInSet: preOpString = "not"; staticCallString = "DafnyRuntime.Set.mem"; break;
        case BinaryExpr.ResolvedOpcode.NotInMultiSet: preOpString = "not"; staticCallString = "DafnyRuntime.Multiset.mem"; break;
        case BinaryExpr.ResolvedOpcode.NotInMap: preOpString = "not"; staticCallString = "DafnyRuntime.Map_.has_key"; break;

        case BinaryExpr.ResolvedOpcode.Union: staticCallString = "DafnyRuntime.Set.union"; break;
        case BinaryExpr.ResolvedOpcode.MultiSetUnion: staticCallString = "DafnyRuntime.Multiset.union"; break;
        case BinaryExpr.ResolvedOpcode.MapMerge: staticCallString = "DafnyRuntime.Map_.merge"; break;
        case BinaryExpr.ResolvedOpcode.Intersection: staticCallString = "DafnyRuntime.Set.intersect"; break;
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection: staticCallString = "DafnyRuntime.Multiset.intersect"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference: staticCallString = "DafnyRuntime.Set.difference"; break;
        case BinaryExpr.ResolvedOpcode.MultiSetDifference: staticCallString = "DafnyRuntime.Multiset.difference"; break;
        case BinaryExpr.ResolvedOpcode.MapSubtraction: staticCallString = "DafnyRuntime.Map_.subtract"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix: staticCallString = "DafnyRuntime.Seq.is_proper_prefix"; break;
        case BinaryExpr.ResolvedOpcode.Prefix: staticCallString = "DafnyRuntime.Seq.is_prefix"; break;
        case BinaryExpr.ResolvedOpcode.Concat: staticCallString = "DafnyRuntime.Seq.concat"; break;
        case BinaryExpr.ResolvedOpcode.InSeq: staticCallString = "DafnyRuntime.Seq.contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSeq: preOpString = "not"; staticCallString = "DafnyRuntime.Seq.contains"; reverseArguments = true; break;

        default:
          Contract.Assert(false); throw new Cce.UnreachableException();
      }
      _ = isNumeric;
    }

    // A tail-recursive method/function is compiled by wrapping its body in a `while true` loop:
    // the call site (TrTailCall, in the base class) reassigns the formal `ref`s and then "jumps
    // to the start" by raising Tailcall, which is caught right around the loop body, causing the
    // `while` to simply run again with the (now updated) formal values. Normal, non-tail-call
    // completion of the body raises the stdlib's `Exit` to escape the loop instead.
    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      wr.Write("(try ");
      var outerBody = wr.NewBlock("while true do", "done", BlockStyle.Newline, BlockStyle.Newline);
      wr.WriteLine("with Exit -> ());");
      return outerBody.NewBlock("(try begin", "raise Exit end with DafnyRuntime.Tailcall -> ())", BlockStyle.Newline, BlockStyle.Newline);
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("raise DafnyRuntime.Tailcall;");
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write("(DafnyRuntime.Int.equal {0} DafnyRuntime.Int.zero)", varName);
    }

    protected override void EmitConversionExpr(Expression fromExpr, Type fromType, Type toType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var fromT = fromType.NormalizeToAncestorType();
      var toT = toType.NormalizeToAncestorType();
      if (fromT.IsCharType && toT.IsNumericBased(Type.NumericPersuasion.Int)) {
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write(" |> DafnyRuntime.Int.of_int");
      } else if (fromT.IsNumericBased(Type.NumericPersuasion.Int) && toT.IsCharType) {
        wr.Write("(DafnyRuntime.Int.to_int (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write("))");
      } else if (fromT.IsNumericBased(Type.NumericPersuasion.Int) && toT.IsNumericBased(Type.NumericPersuasion.Real)) {
        wr.Write("(Q.of_bigint (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write("))");
      } else if (fromT.IsNumericBased(Type.NumericPersuasion.Real) && toT.IsNumericBased(Type.NumericPersuasion.Int)) {
        wr.Write("(Q.to_bigint (");
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        wr.Write("))");
      } else {
        // identity conversion: every other numeric type shares the same (Z.t) representation
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
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
        wr.Write("(DafnyRuntime.Set.of_list [");
        wr.Comma("; ", elements, e => wr.Append(Expr(e, inLetExprBody, wStmts)));
        wr.Write("])");
      } else if (ct is MultiSetType) {
        wr.Write("(DafnyRuntime.Multiset.of_seq [|");
        wr.Comma("; ", elements, e => wr.Append(Expr(e, inLetExprBody, wStmts)));
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
      wr.Write("[");
      wr.Comma("; ", elements, p => {
        wr.Write("(");
        wr.Append(Expr(p.A, inLetExprBody, wStmts));
        wr.Write(", ");
        wr.Append(Expr(p.B, inLetExprBody, wStmts));
        wr.Write(")");
      });
      wr.Write("]");
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
      wr.Write("{0} := (", collName);
      var w = wr.Fork();
      wr.WriteLine(") :: !{0};", collName);
      return w;
    }

    protected override void GetCollectionBuilder_Build(CollectionType ct, IOrigin tok, string collName,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmt) {
      if (ct is SetType) {
        wr.Write("(DafnyRuntime.Set.of_list !{0})", collName);
      } else {
        wr.Write("!{0}", collName);
      }
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ExactBoundedPool);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    // ----- print/toString ------------------------------------------------------------------

    // Since OCaml has no runtime type reflection, printing is done by generating, at each call
    // site, an expression that converts the (statically known) Dafny type to a string.
    private ConcreteSyntaxTree ExprToString(Type type, ConcreteSyntaxTree valueExpr) {
      var t = type.NormalizeExpand();
      var result = new ConcreteSyntaxTree();
      if (t is BoolType) {
        result.Write("(if (");
        result.Append(valueExpr);
        result.Write(") then \"true\" else \"false\")");
      } else if (t is CharType) {
        result.Write("(DafnyRuntime.Char_.to_string (");
        result.Append(valueExpr);
        result.Write("))");
      } else if (t is IntType or BigOrdinalType or BitvectorType) {
        result.Write("(DafnyRuntime.Int.to_string (");
        result.Append(valueExpr);
        result.Write("))");
      } else if (t is RealType) {
        result.Write("(Q.to_string (");
        result.Append(valueExpr);
        result.Write("))");
      } else if (t.AsNewtype is { } ntd) {
        return ExprToString(ntd.ConcreteBaseType(t.TypeArgs), valueExpr);
      } else if (t is SeqType seqT && seqT.Arg.NormalizeExpand() is CharType) {
        result.Write("(DafnyRuntime.Seq.string_of_chars (");
        result.Append(valueExpr);
        result.Write("))");
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
        result.Write("))) ^ \"}\")");
      } else if (t is MultiSetType msT) {
        result.Write("(\"multiset{\" ^ String.concat \", \" (List.concat_map (fun (__v, __n) -> List.init (DafnyRuntime.Int.to_int __n) (fun _ -> ");
        result.Append(ExprToString(msT.Arg, ConcreteSyntaxTree.Create($"__v")));
        result.Write(")) (");
        result.Append(valueExpr);
        result.Write("))) ^ \"}\")");
      } else if (t is MapType mapT) {
        result.Write("(\"map[\" ^ String.concat \", \" (List.map (fun (__k, __v) -> (");
        result.Append(ExprToString(mapT.Domain, ConcreteSyntaxTree.Create($"__k")));
        result.Write(") ^ \" := \" ^ (");
        result.Append(ExprToString(mapT.Range, ConcreteSyntaxTree.Create($"__v")));
        result.Write(")) (");
        result.Append(valueExpr);
        result.Write("))) ^ \"]\")");
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
      } else if (t is UserDefinedType { ResolvedClass: DatatypeDecl dt }) {
        result.Write("({0} (", DatatypeToStringFunction(dt));
        result.Append(valueExpr);
        result.Write("))");
      } else if (t.IsRefType) {
        result.Write("(ignore (");
        result.Append(valueExpr);
        result.Write("); \"<object>\")");
      } else {
        // A bare/erased type parameter or other type we can't recursively format: best effort.
        result.Write("\"<value>\"");
      }
      return result;
    }

    private readonly Dictionary<DatatypeDecl, string> datatypeToStringFunctions = new();

    private string DatatypeToStringFunction(DatatypeDecl dt) {
      if (datatypeToStringFunctions.TryGetValue(dt, out var name)) {
        return name;
      }
      var flatName = FlatName(dt);
      name = flatName + ModuleSeparator + "ToString";
      datatypeToStringFunctions[dt] = name;
      var header = $"{name} (__v : {TypeParamString(dt.TypeArgs)}{flatName}_t)";
      var w = NewValueDecl(header);
      w.Write("match __v with ");
      var sep = "";
      foreach (var ctor in dt.Ctors) {
        w.Write(sep);
        sep = " | ";
        var nonGhost = ctor.Formals.Where(f => !f.IsGhost).ToList();
        if (nonGhost.Count == 0) {
          w.Write("{0} -> \"{1}\"", CtorName(ctor), ctor.Name);
        } else {
          var names = nonGhost.Select((_, i) => $"__a{i}").ToList();
          w.Write("{0} ({1}) -> \"{2}(\" ^ ", CtorName(ctor), string.Join(", ", names), ctor.Name);
          w.Write(string.Join(" ^ \", \" ^ ", names.Zip(nonGhost, (nm, f) => ExprToString(f.Type, ConcreteSyntaxTree.Create($"{nm}")).ToString())));
          w.Write(" ^ \")\"");
        }
      }
      w.WriteLine();
      return name;
    }

    private class ILvalueImpl : ILvalue {
      private readonly OCamlCodeGenerator codeGenerator;
      private readonly Action<ConcreteSyntaxTree> read;
      private readonly Action<ConcreteSyntaxTree, Action<ConcreteSyntaxTree>> write;

      public ILvalueImpl(OCamlCodeGenerator codeGenerator, Action<ConcreteSyntaxTree> read, Action<ConcreteSyntaxTree, Action<ConcreteSyntaxTree>> write) {
        this.codeGenerator = codeGenerator;
        this.read = read;
        this.write = write;
      }

      public void EmitRead(ConcreteSyntaxTree wr) => read(wr);

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        var rhsWriter = new ConcreteSyntaxTree();
        write(wr, w => w.Append(rhsWriter));
        wr.WriteLine(";");
        return rhsWriter;
      }
    }
  }
}
