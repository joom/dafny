// REQUIRES: ocaml
// NONUNIFORM: Focused regression coverage for the unstable OCaml backend
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 --compilers ml "%s"

module Foo {
  function Value(): int {
    1
  }
}

module foo {
  function Value(): int {
    2
  }
}

function F(): int {
  3
}

function f(): int {
  4
}

trait Root<T> extends object {
  function Echo(value: T): T {
    value
  }
}

trait Base<T> extends Root<T> {
  var item: T

  function Keep(value: T): T {
    value
  }

  function Generic<U>(value: U): U {
    value
  }

  const One: int := 1

  method Increment(value: int) returns (result: int) {
    result := value + 1;
  }
}

class Implementation<T> extends Base<T> {
  constructor(value: T) {
    item := value;
  }
}

class Defaults<T(0)> {
  var value: T
}

method Main() {
  var implementation := new Implementation<int>(7);
  var base: Base<int> := implementation;
  var root: Root<int> := implementation;
  var incremented := base.Increment(4);
  var keep := base.Keep;
  var generic := base.Generic<string>;
  print base.item, " ", keep(8), " ", generic("ok"), " ",
    base.One, " ", incremented, " ", root.Echo(9), "\n";

  base.item := 10;
  print implementation.item, "\n";

  var defaults := new Defaults<int>;
  print defaults.value, "\n";

  var same1: object := implementation;
  var same2: object := implementation;
  var different: object := new Implementation<int>(7);
  print same1 == same2, " ", same1 == different, "\n";

  print Foo.Value(), " ", foo.Value(), " ", F(), " ", f(), "\n";
}
