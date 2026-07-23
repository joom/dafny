---
title: Dafny compilation to OCaml
---

Dafny compilation to OCaml
===========================

The OCaml backend is selected with `--target:ml`. It is currently an
**unstable** backend: ordinary verified Dafny programs are supported, but the
backend is not yet feature-complete and is skipped by the default
all-compilers test sweep.

The implementation deliberately favors a small, readable compiler and runtime
over idiomatic generated OCaml or asymptotically efficient collections. The
main sources are:

- `Source/DafnyCore/Backends/OCaml/OCamlBackend.cs`
- `Source/DafnyCore/Backends/OCaml/OCamlCodeGenerator.cs`
- `Source/DafnyRuntime/DafnyRuntimeOCaml/dafnyRuntime.ml`

Compiling and running
---------------------

The backend targets OCaml 4.14 and invokes `ocamlfind ocamlopt`. The native
compiler, findlib, and the Zarith package must be available on `PATH`. With
opam, the additional library can be installed with `opam install zarith`.

```console
dafny run --target:ml Example.dfy
dafny build --target:ml Example.dfy
```

`build` emits `Example.ml` and `Example.exe`, plus one `.ml` file per
non-default Dafny module. Additional `.ml` inputs are accepted. This is not
Dafny separate compilation: all Dafny source is still translated as one
program.

`ocamlopt` normally writes `.cmi`, `.cmx`, and `.o` files beside its inputs.
The backend instead copies the runtime, generated modules, additional inputs,
and main source into a private temporary directory. Only the requested
executable is written to the output directory. The main source is staged
under a valid OCaml compilation-unit name, so Dafny filenames containing
characters such as `-` do not cause OCaml warning 24.

Value representations
---------------------

- `bool` is OCaml `bool`.
- `int`, `ORDINAL`, bit vectors, and native integer types all use Zarith
  `Z.t`. Bit-vector operations still truncate to their declared width.
- `real` uses Zarith `Q.t`, preserving exact rational arithmetic. `Floor`
  follows Dafny semantics, including negative values. Printing follows Dafny's
  textual convention: a real whose reduced denominator has prime factors other
  than 2 and 5 prints as an unevaluated fraction (e.g. `(20.0 / 3.0)`), and
  anything else prints as an exact terminating decimal.

  Note that `Q.t` keeps rationals in lowest terms, so printing agrees with the
  Go and Python backends (which likewise use normalizing rational types) but
  not always with C# and Java, whose `BigRational` does not reduce. For example
  `9.0 / 6.0` prints as `1.5` here, as it does under Go and Python, but as
  `(9.0 / 6.0)` under C#. A test that prints a non-reduced real therefore
  cannot share one `.expect` file across all backends.
- `char` is an OCaml `int`. With `--unicode-char=true` it contains a Unicode
  scalar value; in legacy mode it contains a UTF-16 code unit. Strings and
  character sequences are converted to and from UTF-8 at the OCaml boundary.
- `seq<T>` is an OCaml `'a array`. Updates copy the array.
- A one-dimensional Dafny array uses an OCaml `'a array` as mutable backing
  storage. Multi-dimensional arrays use an `ArrayN.t` record with dimensions
  and a row-major flat backing array.
- Every Dafny array reference, including a statically non-null one, is
  option-wrapped. `None` represents `null`; a non-null auto-initialized array
  is an empty array wrapped in `Some`.
- `set<T>` is a deduplicated list.
- `multiset<T>` is a list of element/multiplicity pairs without zero
  multiplicities.
- `map<K,V>` is an association list without duplicate keys. `Keys`, `Values`,
  and `Items` construct the corresponding Dafny sets.
- Tuples use native OCaml tuples. Zero-tuples use `unit`, and a one-component
  Dafny tuple is represented by its component.
- Datatypes use OCaml variants. Codatatypes use variants under `Lazy.t`, so
  corecursive construction remains lazy.
- Newtypes and subset types erase to their base representation, while their
  compiled witnesses and constraint predicates remain available through
  companion values.
- Class and trait references are option-wrapped records. `object` is
  `Obj.t option` containing a class identity token or an array identity.

Collection operations and equality use Dafny semantics rather than OCaml
structural equality. In particular, set/map order is irrelevant, datatype and
tuple fields are compared recursively, type parameters use their descriptors,
and classes, traits, arrays, and `object` use reference identity. The
list-based collection representations keep the runtime simple but make many
operations linear or quadratic.

Generics and type descriptors
-----------------------------

OCaml type parameters preserve static polymorphism. Where compiled Dafny
semantics need information about a type parameter, generated code also passes
a runtime descriptor containing:

- a default-value constructor,
- semantic equality, and
- conversion to a Dafny-formatted string.

Descriptors support generic auto-initialization, equality in generic
collections and datatypes, and printing generic values. Class and trait
records retain descriptors needed by instance members; static members,
datatype helpers, and generic member tear-offs receive them explicitly.

Declarations, modules, and names
--------------------------------

Each explicit Dafny module becomes an OCaml compilation unit. The default
module is folded into the main `.ml` file. Generated module basenames encode
case, so modules such as `Foo` and `foo` remain distinct on case-insensitive
filesystems.

Within a compilation unit, class records and datatype variants are emitted as
one recursive `type ... and ...` group. Top-level values are handled
differently: the compiler builds their dependency graph, orders its strongly
connected components, and emits `let rec ... and ...` only for values that
are genuinely recursive. Non-recursive values remain ordinary `let`
bindings, preserving OCaml generalization and avoiding the value restriction.
Dependency scanning ignores strings and nested OCaml comments.

All Dafny names are encoded injectively. Compound names length-prefix their
components, and constructors include their enclosing datatype, so source
case, underscores, shared constructor names, and delimiter-like text cannot
collide after flattening. Cross-module references use an OCaml module
qualifier.

Locals, calls, and control flow
-------------------------------

Every local variable and formal parameter is compiled to an OCaml `ref`.
Reads use `!` and assignments use `:=`. This is intentionally less idiomatic
than rebinding immutable values, but closely matches Dafny's mutable statement
model.

Calls use one uniform argument value:

- no arguments use `unit`,
- one argument uses that argument directly, and
- multiple arguments use a tuple.

For a direct instance body, the receiver participates in the same value as
the explicit arguments. Class records also contain closures for instance
functions, methods, and constants. Trait records act as vtables: callable
members are closures, mutable fields are getter/setter closures, and an
upcast preserves the original identity token and type descriptors. This
supports dynamic dispatch through inherited and generic traits, including
default implementations and member tear-offs.

`break`, `continue`, tail-call jumps, early returns, `halt`, and
`try`/`recover` use dedicated OCaml exceptions. Ordinary statement blocks use
`begin ... end`. Non-sequentializable `forall` statements first collect their
type-erased assignment ingredients and apply them after enumeration, matching
the backend framework's alias-safe strategy.

Compiled bounds
---------------

Compiled quantifiers, comprehensions, and assign-such-that constructs consume
lazy OCaml `Stdlib.Seq.t` bounds. Supported bounds include:

- all combinations of lower- and upper-bounded integer ranges,
- booleans and characters,
- elements of sequences, sets, multisets, and maps,
- all subsets of a finite set,
- exact-value bounds, and
- all constructors of a finite datatype.

`exists` and `forall` short-circuit. Character enumeration follows the chosen
Unicode or legacy UTF-16 mode.

Known limitations
-----------------

The feature-support table in the Dafny reference is authoritative. The main
unsupported areas are:

- Iterators. OCaml 4.14 has no effect-handler/coroutine mechanism that can
  directly resume a Dafny iterator after `yield`; a thread-based emulation is
  intentionally outside this backend's current scope.
- Runtime type-test expressions (`x is T`), subset-type tests, and
  trait-to-class downcasts.
- Quantifier and comprehension bounds that narrow a reference type, such as
  `set x: C | x in s` where `s` has a trait element type. Filtering these
  needs the same dynamic type test as `x is T`.
- External classes, external constructors, and external modules whose name
  consists only of underscores.
- Separate Dafny compilation.
- Dafny standard libraries and the `ActionsExterns` standard-library layer.
- Method synthesis, execution coverage reports, and placing every compiled
  built-in type in the runtime library.

Unsupported features are reported through Dafny's normal backend feature
diagnostics rather than failing later in generated OCaml.
