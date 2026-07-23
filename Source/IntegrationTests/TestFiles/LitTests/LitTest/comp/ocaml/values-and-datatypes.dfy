// REQUIRES: ocaml
// NONUNIFORM: Focused regression coverage for the unstable OCaml backend
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 --compilers ml "%s" -- --unicode-char=true

function Identity<T>(value: T): T {
  value
}

function IntValue(): int {
  Identity(1)
}

function BoolValue(): bool {
  Identity(true)
}

datatype First = Same(value: int) | Empty
datatype Second = Same(value: int) | Other
datatype Shared = A(value: int) | B(value: int)
datatype Color = Red | Green | Blue

type NonEmpty<T> = values: seq<T> | |values| > 0 witness *

method Main() {
  print IntValue(), " ", BoolValue(), "\n";

  var fraction: real := 2.0 / 3.0;
  print fraction > 3.0 / 100.0, " ", fraction, " ", (-1.5).Floor, "\n";

  var second := Second.Same(3);
  var shared := Shared.B(4);
  print second, " ", shared.value, "\n";

  print forall color: Color :: color.Red? || color.Green? || color.Blue?, "\n";
  print exists color: Color :: color.Green?, "\n";
  print exists values: NonEmpty<int> {:trigger values[0]} :: values == [1], "\n";

  var subsets := set values: set<int> | values <= {1, 2} :: values;
  print |subsets|, "\n";

  print '\U{1F60E}', " ", |"\U{1F60E}"|, "\n";
}
