---
title: Dafny compilation to OCaml
---

Dafny compilation to OCaml
===========================

The OCaml backend (`--target:ml`) favors simplicity and readability of the
implementation over performance and completeness. If you're reading the
compiler source to understand how it works, `Source/DafnyCore/Backends/OCaml/`
and `Source/DafnyRuntime/DafnyRuntimeOCaml/dafnyRuntime.ml` are much shorter
than the other backends, at some cost in idiomaticity and a handful of
semantic gaps described below.

Compiling and running
----------------------

```
dafny run --target:ml Example.dfy
dafny build --target:ml Example.dfy   # produces Example.ml (and Example.exe)
```

The backend shells out to `ocamlfind ocamlopt` with the [Zarith](https://github.com/ocaml/Zarith)
package, so an OCaml toolchain (`ocamlfind`, `ocamlopt`) with `zarith` installed
(`opam install zarith`) needs to be on `PATH`.

Representation of Dafny values
-------------------------------

Every Dafny type is represented as an ordinary, unparameterized OCaml value —
there is no runtime type-descriptor machinery:

  - `bool` is `bool`.
  - `char` is a plain OCaml `int` holding a Unicode code point (regardless of
    whether `--unicode-char` is set).
  - `int`, `nat`, bit-vector types, and native integer types (`int32`, etc.)
    are *all* represented uniformly as Zarith's arbitrary-precision `Z.t`.
    There's no `int`/`bv32`/`uint64` distinction in the generated code, and no
    overflow checking is skipped for "native" types the way it is in some
    other backends — everything just uses unbounded arithmetic.
  - `real` is Zarith's arbitrary-precision rational `Q.t`.
  - `seq<T>` and `array<T>` are both plain OCaml `'a array`. A `seq` is
    conceptually immutable — operations like `s + t` or `s[i := v]` always
    allocate a new array — while an `array<T>` is mutated in place.
  - `string` is `seq<char>`, i.e. `int array`.
  - `set<T>` is a deduplicated `'a list`.
  - `multiset<T>` is a `(element, multiplicity) list`, kept free of
    zero-multiplicity entries.
  - `map<K, V>` is a `(key, value) list` association list, kept free of
    duplicate keys.
  - Tuples are native OCaml tuples.
  - A `datatype` compiles to an OCaml variant type, one constructor per
    Dafny constructor, with the constructor's non-ghost formals as plain
    positional (tupled) arguments — e.g. `datatype Tree = Leaf | Node(Tree,
    int, Tree)` compiles to `type tree_t = Leaf | Node of tree_t * Int.t *
    tree_t`.
  - A `class` compiles to a mutable OCaml record.

All of the above live in a single runtime module (`DafnyRuntime`, from
`dafnyRuntime.ml`) with straightforward implementations — e.g. `set`
operations are `O(n)` list scans, not a balanced-tree `Set.Make`. This keeps
the runtime a single short, ordinary-looking file, at a real performance
cost for large collections.

Everything is one file, one flat namespace
--------------------------------------------

Dafny's modules, classes, and datatypes are *not* translated to OCaml
modules. Instead, every top-level Dafny declaration is flattened into one
long `type ... and ... and ...` block (all record/variant declarations) and
one long `let rec ... and ... and ...` block (all function/method bodies),
covering the whole program. Every name is mangled with its enclosing
module and class/datatype name to keep it unique (e.g. a `Node` field
`left` on a class in module `M` becomes the record field `m__Node__left`).

This is the main way this backend trades idiomaticity for simplicity: real
OCaml code would use nested modules matching Dafny's module structure, and
`and`-chaining the entire program's functions together (rather than only the
functions that are actually mutually recursive) is not how anyone would
write OCaml by hand. But it means the compiler never has to worry about
*declaration order* (OCaml normally requires "define before use"; Dafny does
not) or about generating nested `module M = struct ... end` blocks correctly.

Everything is a `ref`
-----------------------

Every local variable and formal parameter compiles to an OCaml `ref` cell:
a Dafny declaration `var x := 5;` becomes `let x = ref (DafnyRuntime.Int.of_string "5") in`,
reads of `x` become `!x`, and assignments become `x := ...`. This is not
idiomatic OCaml (real OCaml code would use `let`-rebinding and avoid mutable
state wherever possible) but it means the compiler doesn't need to track
which Dafny bindings are actually reassigned — every binding is treated
uniformly, which keeps the statement-compiling code simple.

Instance methods and fields
-----------------------------

Because Dafny methods and functions can take any number of arguments, calls
compile to a uniform convention based on how many non-ghost arguments there
are: zero arguments compiles to a `unit` parameter (`f ()`), exactly one
compiles to a bare parameter (`f x`), and two or more compile to a single
tupled parameter (`f (x, y)`). This exactly matches how a Dafny call
`f(x, y)` reads as OCaml source (function application to the tuple `(x,
y)`), so call sites don't need special-casing based on arity.

Instance (non-`static`) methods and functions are compiled as ordinary
top-level functions taking the receiver as an explicit first argument (e.g.
`let counter__increment this amt = ...`). However, since Dafny always
compiles an instance call as `receiver.name(args)`, every class record also
carries one closure field per instance method/function, each wired up to
call the corresponding top-level function with the record itself as the
receiver (constructed via a self-referential `let rec this = { ...;
increment = (fun amt -> counter__increment this amt) } in this`). So
`c.Increment(5)` compiles to the perfectly ordinary-looking record field
call `c.increment(5)`, which just happens to close over `c` already.

Traits (and therefore any kind of dynamic dispatch or subtyping between
classes) are not supported, so there's no need for these closures to support
overriding.

Control flow
-------------

`if`/`while`/blocks compile using `begin ... end` (OCaml's parenthesization
keywords) in place of C-style `{ ... }`, with Dafny statement sequences
becoming OCaml `;`-separated sequences (each "statement" is unit-typed).

`break`/`continue`/early `return` (and the multi-branch bodies functions with
`match` or `if`-expressions compile to) all use OCaml exceptions:
`raise Dafny_break_<label>` / `Dafny_continue_<label>`, caught by a `try`
wrapped around the applicable loop or labeled statement, and
`raise (DafnyRuntime.Return (Obj.repr value))`, caught once by a `try`
wrapped around the whole body of every method, function, and lambda. This
means a plain `let () = ...` control-flow style (which is how idiomatic
OCaml would compile a function with several `if`/`match` branches, each
simply being the tail expression of its branch) isn't used — every
Dafny function's body is compiled the same way regardless of whether it's a
single expression or requires early returns, again trading idiomaticity for
uniformity.

A tail-recursive Dafny function/method (`f.IsTailRecursive`) is compiled by
wrapping its body in `while true do ... done`: the call site reassigns the
formal `ref`s and "jumps to the top" by raising a dedicated exception caught
immediately around the loop body. In practice, OCaml's native tail-call
optimization would have handled a simple self-recursive call in tail
position just as well without this — but the `while`-loop form is what
`EmitJumpToTailCallStart` naturally compiles to given the framework's
"reassign formals, then jump" calling convention.

Known limitations
-------------------

Compared to the more complete backends (C#, Java, Go, ...), this backend does
not support:

  - **Traits**, and therefore no dynamic dispatch, virtual methods, or
    upcasting/downcasting between class types.
  - **Co-inductive datatypes** (codatatypes) or **iterators**.
  - **Multi-dimensional arrays** (only `array<T>`, not `array2<T>` etc.).
  - Compiled **quantifiers**, **map comprehensions**, or **assign-such-that**
    (`:|`) expressions.
  - **`forall` statements that can't be sequentialized** (the ones that need
    to build up a list of "ingredient" tuples before applying them).
  - **`null` is not a distinguished value.** There's no OCaml analogue of a
    null pointer for a plain record, so `null` compiles to a fresh
    all-default instance of the class rather than a sentinel value. This
    means `x == null` is not reliable — it's a physical-equality check, and
    a freshly-built default instance is never `==` to any other instance,
    including another evaluation of `null` itself. Code that checks
    `x == null` before *setting* `x`, or that never compares against `null`
    at all, works fine; code that relies on `x == null` being true after
    `x := null` does not.
  - Extern declarations / FFI to hand-written OCaml code.

Programs that stay within ordinary functional/imperative Dafny — classes,
datatypes, generics, closures, collections, arithmetic — are expected to
work.
