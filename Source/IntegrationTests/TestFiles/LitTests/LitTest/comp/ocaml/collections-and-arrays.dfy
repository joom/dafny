// REQUIRES: ocaml
// NONUNIFORM: Focused regression coverage for the unstable OCaml backend
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 --compilers ml "%s"

class Element {}

method Main() {
  var one := {1, 2};
  var reordered := {2, 1};
  print one == reordered, " ", |{one, reordered}|, "\n";

  var mapWithDuplicateValues := map[1 := 0, 2 := 0];
  print |mapWithDuplicateValues.Values|, "\n";

  var nullable: array?<int> := null;
  var numbers := new int[2](i => i + 4);
  var widened: array?<int> := numbers;
  print nullable == null, " ", widened != null, "\n";
  print numbers.Length, " ", numbers[..], "\n";

  var same1: object := numbers;
  var same2: object := numbers;
  var other: object := new int[2];
  print same1 == same2, " ", same1 == other, "\n";

  var matrix := new int[2, 3];
  matrix[1, 2] := 7;
  print matrix.Length0, " ", matrix.Length1, " ", matrix[1, 2], "\n";

  var first := new Element;
  var second := new Element;
  var references := {first, second};
  print first in references, " ", |references|, "\n";
}
