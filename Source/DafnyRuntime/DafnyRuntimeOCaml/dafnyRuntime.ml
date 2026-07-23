(* Dafny runtime support for the OCaml backend.

   Design (see docs/Compilation/OCaml.md for the rationale):
   - Dafny's `int` and all bit-vector/native integer types are represented
     uniformly as Zarith's arbitrary-precision [Z.t].
   - Dafny's `real` is represented as Zarith's arbitrary-precision rational [Q.t].
   - Dafny's `char` is represented as an OCaml [int], holding either a Unicode scalar value or
     a UTF-16 code unit according to the compiler's [--unicode-char] mode.
   - `seq<T>` is represented as an OCaml ['a array]. Array storage uses the same representation
     (or an [ArrayN.t] for multiple dimensions), but every Dafny array reference is
     option-wrapped so [None] represents [null]. A seq is conceptually immutable; the compiler
     copies on updates and when deriving a seq from mutable array storage.
   - `set<T>` is a deduplicated ['a list].
   - `multiset<T>` is a [('a * Z.t) list] of (element, multiplicity) pairs, kept free
     of zero-multiplicity entries.
   - `map<K, V>` is a ['(K * V) list] association list, kept free of duplicate keys.
   - Class/trait records and opaque [object] values carry stable physical identity; all
     reference types are option-wrapped, with [None] for [null].

   Binary operators (`DafnyRuntime.Int.add`, `DafnyRuntime.Set.union`, etc.) are all called
   from generated code as `f (a, b)` (a single tuple argument), because that's the calling
   convention the OCaml backend uses uniformly for every Dafny function/method with more than
   one argument (see OCamlCodeGenerator's class comment). So every binary function below takes
   a tuple, not two curried arguments.
*)

exception Halt of string

(* Raised by a tail-recursive method/function to jump back to the top of its own body; see
   OCamlCodeGenerator.EmitTailCallStructure/EmitJumpToTailCallStart. *)
exception Tailcall

(* Raised to implement "early return": a `return` statement, or a match/if branch of a function
   body that isn't in tail position, both compile to raising this (with the result value boxed
   via Obj.repr, since OCaml exceptions can't be polymorphic); every method/function body is
   wrapped in a handler that unboxes it right back with Obj.magic. See
   OCamlCodeGenerator.CreateSubroutine/EmitReturn/EmitReturnExpr. *)
exception Return of Obj.t

let halt (msg : string) : 'a = raise (Halt msg)

let equal (equal_value : 'a -> 'b -> bool) ((a, b) : 'a * 'b) : bool =
  equal_value a b

(* OCaml has no null function value.  Keep a unique, non-callable heap object for the default
   value of Dafny's nullable arrow types.  Generated printing code can recognize it by physical
   identity, while the type system only ever sees it after [Obj.magic] at an arrow type. *)
let null_function_marker : Obj.t = Obj.repr (ref ())

(* Every generated class and trait record starts with the same four fields, in this order:
     0  <flat-name>__dummy   (per-record, keeps the record non-empty)
     1  d_dafny_id
     2  d_dafny_type_name
     3  d_dafny_object
   See OCamlCodeGenerator.CreateClass/CreateTrait, which are what would break these three
   functions if the prefix ever changed. Reading them positionally rather than by label keeps
   these operations polymorphic: naming a label would force every record type they are applied
   to to unify merely because they all share d_dafny_id. *)
let reference_id (value : 'a) : Obj.t = Obj.field (Obj.repr value) 1

let reference_type_name (value : 'a) : string =
  Obj.obj (Obj.field (Obj.repr value) 2)

let reference_object (value : 'a) : Obj.t =
  Obj.field (Obj.repr value) 3

type object_box = { object_id : Obj.t; object_value : Obj.t }

let box_object (id : Obj.t) (value : Obj.t) : Obj.t =
  Obj.repr { object_id = id; object_value = value }

let unbox_object_id (boxed : Obj.t) : Obj.t =
  (Obj.obj boxed : object_box).object_id

let unbox_object_value (boxed : Obj.t) : Obj.t =
  (Obj.obj boxed : object_box).object_value

let fresh_object () : Obj.t =
  let identity = ref () in
  box_object (Obj.repr identity) (Obj.repr identity)

module TypeDescriptor = struct
  type 'a t = {
    default : unit -> 'a;
    equal : 'a -> 'a -> bool;
    to_string : 'a -> string;
  }
end

(* ----- integers ----- *)

module Int = struct
  type t = Z.t

  let zero = Z.zero
  let of_int = Z.of_int
  let of_string = Z.of_string
  let to_int = Z.to_int
  let to_string = Z.to_string
  let equal = Z.equal
  let compare = Z.compare
  let succ = Z.succ
  let pred = Z.pred
  let lognot = Z.lognot

  let add ((a, b) : t * t) : t = Z.add a b
  let sub ((a, b) : t * t) : t = Z.sub a b
  let mul ((a, b) : t * t) : t = Z.mul a b
  let ediv ((a, b) : t * t) : t = Z.ediv a b
  let erem ((a, b) : t * t) : t = Z.erem a b
  let logand ((a, b) : t * t) : t = Z.logand a b
  let logor ((a, b) : t * t) : t = Z.logor a b
  let logxor ((a, b) : t * t) : t = Z.logxor a b
  let shift_left ((x, n) : t * t) : t = Z.shift_left x (Z.to_int n)
  let shift_right ((x, n) : t * t) : t = Z.shift_right x (Z.to_int n)
  let lt ((a, b) : t * t) : bool = Z.lt a b
  let le ((a, b) : t * t) : bool = Z.leq a b
  let ge ((a, b) : t * t) : bool = Z.geq a b
  let gt ((a, b) : t * t) : bool = Z.gt a b

  (* Dafny characters are Unicode code points, represented as plain OCaml ints; these let
     char +/- int arithmetic reuse the same DafnyRuntime.Int.add/sub call sites as numbers. *)
  let add_char ((a, b) : int * t) : int = a + Z.to_int b
  let sub_char ((a, b) : int * t) : int = a - Z.to_int b

  (* Dafny bit vectors are unsigned, and this backend erases the signed native integer types
     to plain Z.t without truncating them, so only the unsigned reduction is ever needed. *)
  let truncate (width : int) (x : t) : t = Z.erem x (Z.shift_left Z.one width)

  (* `x` is assumed to already be an unsigned `width`-bit value (0 <= x < 2^width), as every
     bitvector value is between operations (see EmitBitvectorTruncation). *)
  let rotate_left (width : int) (x : t) (amount : t) : t =
    if width = 0 then x
    else
      let k = Z.to_int (Z.erem amount (Z.of_int width)) in
      truncate width (Z.logor (Z.shift_left x k) (Z.shift_right x (width - k)))

  let rotate_right (width : int) (x : t) (amount : t) : t =
    if width = 0 then x
    else
      let k = Z.to_int (Z.erem amount (Z.of_int width)) in
      truncate width (Z.logor (Z.shift_right x k) (Z.shift_left x (width - k)))
end

(* ----- exact real numbers ----- *)

module Real = struct
  type t = Q.t

  let zero = Q.zero
  let of_string (text : string) : t =
    (* Dafny accepts a sign on the fractional token (for example 0.-2 and
       0.000-2). Zarith accepts ordinary signed decimals, so normalize those
       spellings before parsing exactly. *)
    match String.index_from_opt text 1 '-' with
    | Some sign ->
        let unsigned =
          String.sub text 0 sign
          ^ "0"
          ^ String.sub text (sign + 1) (String.length text - sign - 1)
        in
        Q.neg (Q.of_string unsigned)
    | None -> Q.of_string text
  let of_bigint = Q.of_bigint
  let equal ((a, b) : t * t) : bool = Q.equal a b

  let add ((a, b) : t * t) : t = Q.add a b
  let sub ((a, b) : t * t) : t = Q.sub a b
  let mul ((a, b) : t * t) : t = Q.mul a b
  let div ((a, b) : t * t) : t = Q.div a b

  let lt ((a, b) : t * t) : bool = Q.compare a b < 0
  let le ((a, b) : t * t) : bool = Q.compare a b <= 0
  let ge ((a, b) : t * t) : bool = Q.compare a b >= 0
  let gt ((a, b) : t * t) : bool = Q.compare a b > 0

  (* Dafny's conversion from real to int and the .Floor member both round toward negative
     infinity. Z.ediv has exactly that behavior because Q.den is positive. *)
  let floor (q : t) : Z.t = Z.ediv (Q.num q) (Q.den q)

  let to_string (q : t) : string =
    let numerator = Q.num q and denominator = Q.den q in
    if Z.equal denominator Z.one then Z.to_string numerator ^ ".0"
    else begin
      (* Dafny prints a rational as a decimal exactly when its reduced denominator has no prime
         factors other than 2 and 5. *)
      let rec remove_factor n factor count =
        let quotient, remainder = Z.ediv_rem n factor in
        if Z.equal remainder Z.zero then remove_factor quotient factor (count + 1)
        else n, count
      in
      let after_twos, twos = remove_factor denominator (Z.of_int 2) 0 in
      let remaining, fives = remove_factor after_twos (Z.of_int 5) 0 in
      if Z.equal remaining Z.one then begin
        let decimal_places = max twos fives in
        let scaled =
          Z.mul numerator
            (Z.mul
               (Z.pow (Z.of_int 2) (decimal_places - twos))
               (Z.pow (Z.of_int 5) (decimal_places - fives)))
        in
        let sign = if Z.sign scaled < 0 then "-" else "" in
        let digits = Z.to_string (Z.abs scaled) in
        let padding = max 0 (decimal_places + 1 - String.length digits) in
        let digits = String.make padding '0' ^ digits in
        let decimal_point = String.length digits - decimal_places in
        sign
        ^ String.sub digits 0 decimal_point
        ^ "."
        ^ String.sub digits decimal_point decimal_places
      end else
      "(" ^ Z.to_string numerator ^ ".0 / " ^ Z.to_string denominator ^ ".0)"
    end
end

(* ----- characters (Unicode code points, represented as native ints) ----- *)

module Char_ = struct
  let utf8_of_code_point (buf : Buffer.t) (cp : int) : unit =
    let cp =
      if cp < 0 || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF) then 0xFFFD else cp
    in
    if cp < 0x80 then
      Buffer.add_char buf (Char.chr cp)
    else if cp < 0x800 then begin
      Buffer.add_char buf (Char.chr (0xC0 lor (cp lsr 6)));
      Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
    end else if cp < 0x10000 then begin
      Buffer.add_char buf (Char.chr (0xE0 lor (cp lsr 12)));
      Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
      Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
    end else begin
      Buffer.add_char buf (Char.chr (0xF0 lor (cp lsr 18)));
      Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
      Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
      Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
    end

  let to_string (cp : int) : string =
    let buf = Buffer.create 4 in
    utf8_of_code_point buf cp;
    Buffer.contents buf

  let to_literal (cp : int) : string =
    let contents =
      match cp with
      | 0 -> "\\0"
      | 9 -> "\\t"
      | 10 -> "\\n"
      | 13 -> "\\r"
      | 34 -> "\\\""
      | 39 -> "\\'"
      | 92 -> "\\\\"
      | _ -> to_string cp
    in
    "'" ^ contents ^ "'"
end

(* ----- sequences (also used for strings and, when mutated, arrays) ----- *)

module Seq = struct
  let length (s : 'a array) : Z.t = Z.of_int (Array.length s)
  let length_int (s : 'a array) : int = Array.length s

  let create (n : Z.t) (f : Z.t -> 'a) : 'a array =
    Array.init (Z.to_int n) (fun i -> f (Z.of_int i))

  let select ((s, i) : 'a array * Z.t) : 'a = s.(Z.to_int i)

  let update ((s, i, v) : 'a array * Z.t * 'a) : 'a array =
    let s' = Array.copy s in
    s'.(Z.to_int i) <- v;
    s'

  let take ((s, n) : 'a array * Z.t) : 'a array = Array.sub s 0 (Z.to_int n)

  let drop ((s, n) : 'a array * Z.t) : 'a array =
    let i = Z.to_int n in
    Array.sub s i (Array.length s - i)

  let sub ((s, lo, hi) : 'a array * Z.t * Z.t) : 'a array =
    let lo = Z.to_int lo and hi = Z.to_int hi in
    Array.sub s lo (hi - lo)

  let concat ((a, b) : 'a array * 'a array) : 'a array = Array.append a b

  let contains (equal : 'a -> 'b -> bool) ((s, x) : 'b array * 'a) : bool =
    Array.exists (equal x) s

  let equal (equal_element : 'a -> 'b -> bool) ((a, b) : 'a array * 'b array) : bool =
    let n = Array.length a in
    n = Array.length b
    &&
    let rec loop i =
      i = n || (equal_element a.(i) b.(i) && loop (i + 1))
    in
    loop 0

  let is_prefix (equal_element : 'a -> 'b -> bool) ((a, b) : 'a array * 'b array) : bool =
    let n = Array.length a in
    n <= Array.length b
    &&
    let rec loop i =
      i = n || (equal_element a.(i) b.(i) && loop (i + 1))
    in
    loop 0

  let is_proper_prefix (equal_element : 'a -> 'b -> bool)
      ((a, b) : 'a array * 'b array) : bool =
    Array.length a < Array.length b && is_prefix equal_element (a, b)

  let of_string (unicode : bool) (s : string) : int array =
    (* decode UTF-8 into an array of Unicode code points *)
    let n = String.length s in
    let out = ref [] in
    let i = ref 0 in
    while !i < n do
      let c0 = Char.code s.[!i] in
      let cp, len =
        if c0 < 0x80 then (c0, 1)
        else if c0 land 0xE0 = 0xC0 && !i + 1 < n then
          (((c0 land 0x1F) lsl 6) lor (Char.code s.[!i + 1] land 0x3F), 2)
        else if c0 land 0xF0 = 0xE0 && !i + 2 < n then
          ( ((c0 land 0x0F) lsl 12)
            lor ((Char.code s.[!i + 1] land 0x3F) lsl 6)
            lor (Char.code s.[!i + 2] land 0x3F),
            3 )
        else if c0 land 0xF8 = 0xF0 && !i + 3 < n then
          ( ((c0 land 0x07) lsl 18)
            lor ((Char.code s.[!i + 1] land 0x3F) lsl 12)
            lor ((Char.code s.[!i + 2] land 0x3F) lsl 6)
            lor (Char.code s.[!i + 3] land 0x3F),
            4 )
        else (c0, 1)
      in
      if unicode || cp <= 0xFFFF then
        out := cp :: !out
      else begin
        let cp' = cp - 0x10000 in
        let high = 0xD800 + (cp' lsr 10) in
        let low = 0xDC00 + (cp' land 0x3FF) in
        out := low :: high :: !out
      end;
      i := !i + len
    done;
    Array.of_list (List.rev !out)

  let string_of_chars (unicode : bool) (s : int array) : string =
    let buf = Buffer.create (Array.length s) in
    if unicode then
      Array.iter (Char_.utf8_of_code_point buf) s
    else begin
      let i = ref 0 in
      while !i < Array.length s do
        let first = s.(!i) in
        if
          first >= 0xD800 && first <= 0xDBFF
          && !i + 1 < Array.length s
          && s.(!i + 1) >= 0xDC00 && s.(!i + 1) <= 0xDFFF
        then begin
          let cp = 0x10000 + ((first - 0xD800) lsl 10) + (s.(!i + 1) - 0xDC00) in
          Char_.utf8_of_code_point buf cp;
          i := !i + 2
        end else begin
          Char_.utf8_of_code_point buf first;
          incr i
        end
      done
    end;
    Buffer.contents buf

  let string_literal_of_chars (unicode : bool) (s : int array) : string =
    let buf = Buffer.create (Array.length s + 2) in
    Buffer.add_char buf '"';
    let i = ref 0 in
    while !i < Array.length s do
      let escaped =
        match s.(!i) with
        | 0 -> Some "\\0"
        | 9 -> Some "\\t"
        | 10 -> Some "\\n"
        | 13 -> Some "\\r"
        | 34 -> Some "\\\""
        | 39 -> Some "\\'"
        | 92 -> Some "\\\\"
        | _ -> None
      in
      match escaped with
      | Some text ->
          Buffer.add_string buf text;
          incr i
      | None ->
          let width =
            if
              not unicode
              && s.(!i) >= 0xD800 && s.(!i) <= 0xDBFF
              && !i + 1 < Array.length s
              && s.(!i + 1) >= 0xDC00 && s.(!i + 1) <= 0xDFFF
            then 2
            else 1
          in
          Buffer.add_string buf (string_of_chars unicode (Array.sub s !i width));
          i := !i + width
    done;
    Buffer.add_char buf '"';
    Buffer.contents buf
end

(* ----- multi-dimensional arrays (array2, array3, ...) -----
   A single dimension `array<T>` is a plain OCaml `'a array` (see the Seq module below); this is
   only used for `array2<T>`, `array3<T>`, etc. A flat backing array keeps indexing/allocation
   simple (one implementation regardless of dimension count) at the cost of doing the row-major
   index arithmetic by hand instead of relying on nested native arrays. *)

module ArrayN = struct
  type 'a t = { dims : int array; data : 'a array }

  let make (dims : int array) (init : 'a) : 'a t =
    { dims; data = Array.make (Array.fold_left ( * ) 1 dims) init }

  let flat_index (a : 'a t) (idx : int array) : int =
    let n = Array.length idx in
    let rec go i acc = if i >= n then acc else go (i + 1) ((acc * a.dims.(i)) + idx.(i)) in
    go 0 0

  let get (a : 'a t) (idx : int array) : 'a = a.data.(flat_index a idx)

  let set (a : 'a t) (idx : int array) (v : 'a) : unit = a.data.(flat_index a idx) <- v

  let length (a : 'a t) (dim : int) : Z.t = Z.of_int a.dims.(dim)
  let length_int (a : 'a t) (dim : int) : int = a.dims.(dim)
end

(* ----- sets ----- *)

module Set = struct
  let mem_by (equal : 'a -> 'b -> bool) (x : 'a) (s : 'b list) : bool =
    List.exists (equal x) s

  (* Retains first-occurrence order. Accumulating in reverse and reversing once at the end
     avoids the O(n) list copy that [acc @ [x]] would do on every accepted element; the
     membership scan is still linear, so this stays quadratic in comparisons but no longer
     allocates quadratically on top of that. *)
  let of_list (equal : 'a -> 'a -> bool) (l : 'a list) : 'a list =
    List.rev
      (List.fold_left
         (fun acc x -> if mem_by equal x acc then acc else x :: acc)
         [] l)

  let cardinality (s : 'a list) : Z.t = Z.of_int (List.length s)

  let mem (equal : 'a -> 'b -> bool) ((x, s) : 'a * 'b list) : bool =
    mem_by equal x s

  let union (equal : 'a -> 'a -> bool) ((a, b) : 'a list * 'a list) : 'a list =
    (* Match Dafny's deterministic iteration convention: the right operand establishes the
       order, followed by elements unique to the left operand. *)
    b @ List.filter (fun x -> not (mem_by equal x b)) a

  let intersect (equal : 'a -> 'a -> bool) ((a, b) : 'a list * 'a list) : 'a list =
    List.filter (fun x -> mem_by equal x b) a

  let difference (equal : 'a -> 'a -> bool) ((a, b) : 'a list * 'a list) : 'a list =
    List.filter (fun x -> not (mem_by equal x b)) a

  let is_subset (equal : 'a -> 'b -> bool) ((a, b) : 'a list * 'b list) : bool =
    List.for_all (fun x -> mem_by equal x b) a

  let is_proper_subset (equal : 'a -> 'b -> bool) ((a, b) : 'a list * 'b list) : bool =
    is_subset equal (a, b) && List.length a < List.length b

  let is_disjoint (equal : 'a -> 'b -> bool) ((a, b) : 'a list * 'b list) : bool =
    List.for_all (fun x -> not (mem_by equal x b)) a

  let equal (equal_element : 'a -> 'b -> bool) ((a, b) : 'a list * 'b list) : bool =
    List.length a = List.length b && is_subset equal_element (a, b)

  let rec all_subsets (values : 'a list) : 'a list Stdlib.Seq.t =
    match values with
    | [] -> Stdlib.Seq.return []
    | value :: rest ->
        Stdlib.Seq.concat_map
          (fun subset -> List.to_seq [ subset; value :: subset ])
          (all_subsets rest)
end

(* ----- multisets: (element, positive multiplicity) pairs ----- *)

module Multiset = struct
  let normalize (l : ('a * Z.t) list) : ('a * Z.t) list =
    List.filter (fun (_, n) -> Z.gt n Z.zero) l

  let rec find_opt (equal : 'a -> 'b -> bool) (key : 'a) = function
    | [] -> None
    | (candidate, value) :: rest ->
        if equal key candidate then Some value else find_opt equal key rest

  let remove (equal : 'a -> 'a -> bool) (key : 'a) (entries : ('a * 'b) list) =
    List.filter (fun (candidate, _) -> not (equal key candidate)) entries

  (* As with Set.of_list, accumulate in reverse and reverse once, so a new element costs a cons
     rather than a full copy of the accumulator. Retains first-occurrence order. *)
  let of_seq (equal : 'a -> 'a -> bool) (s : 'a array) : ('a * Z.t) list =
    let add acc x =
      if List.exists (fun (candidate, _) -> equal x candidate) acc then
        List.map
          (fun (candidate, count) ->
            if equal x candidate then (candidate, Z.succ count) else (candidate, count))
          acc
      else (x, Z.one) :: acc
    in
    List.rev (Array.fold_left add [] s)

  let of_set (s : 'a list) : ('a * Z.t) list = List.map (fun x -> (x, Z.one)) s

  let multiplicity (equal : 'a -> 'b -> bool) (x : 'a) (m : ('b * Z.t) list) : Z.t =
    match find_opt equal x m with Some n -> n | None -> Z.zero

  let update (equal : 'a -> 'a -> bool)
      ((x, n, m) : 'a * Z.t * ('a * Z.t) list) : ('a * Z.t) list =
    if Z.leq n Z.zero then remove equal x m
    else if List.exists (fun (candidate, _) -> equal x candidate) m then
      List.map
        (fun (candidate, count) ->
          if equal x candidate then (candidate, n) else (candidate, count))
        m
    else m @ [ (x, n) ]

  let cardinality (m : ('a * Z.t) list) : Z.t =
    List.fold_left (fun acc (_, n) -> Z.add acc n) Z.zero m

  let all_keys (equal : 'a -> 'a -> bool)
      (a : ('a * Z.t) list) (b : ('a * Z.t) list) : 'a list =
    Set.of_list equal (List.map fst a @ List.map fst b)

  let union (equal : 'a -> 'a -> bool)
      ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : ('a * Z.t) list =
    List.map
      (fun x -> (x, Z.add (multiplicity equal x a) (multiplicity equal x b)))
      (Set.of_list equal (List.map fst b @ List.map fst a))

  let intersect (equal : 'a -> 'a -> bool)
      ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : ('a * Z.t) list =
    normalize
      (List.map
         (fun x -> (x, Z.min (multiplicity equal x a) (multiplicity equal x b)))
         (all_keys equal a b))

  let difference (equal : 'a -> 'a -> bool)
      ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : ('a * Z.t) list =
    normalize
      (List.map
         (fun x -> (x, Z.sub (multiplicity equal x a) (multiplicity equal x b)))
         (all_keys equal a b))

  let is_subset (equal : 'a -> 'b -> bool)
      ((a, b) : ('a * Z.t) list * ('b * Z.t) list) : bool =
    List.for_all
      (fun (x, count) -> Z.leq count (multiplicity equal x b))
      a

  let is_proper_subset (equal : 'a -> 'b -> bool)
      ((a, b) : ('a * Z.t) list * ('b * Z.t) list) : bool =
    is_subset equal (a, b) && Z.lt (cardinality a) (cardinality b)

  let is_disjoint (equal : 'a -> 'b -> bool)
      ((a, b) : ('a * Z.t) list * ('b * Z.t) list) : bool =
    List.for_all
      (fun (x, _) -> Z.equal (multiplicity equal x b) Z.zero)
      a

  let equal (equal_element : 'a -> 'b -> bool)
      ((a, b) : ('a * Z.t) list * ('b * Z.t) list) : bool =
    List.length a = List.length b
    && List.for_all
         (fun (x, count) -> Z.equal count (multiplicity equal_element x b))
         a

  let mem (equal : 'a -> 'b -> bool) ((x, m) : 'a * ('b * Z.t) list) : bool =
    Z.gt (multiplicity equal x m) Z.zero

  let map (equal_result : 'b -> 'b -> bool) (convert : 'a -> 'b)
      (source : ('a * Z.t) list) : ('b * Z.t) list =
    List.fold_left
      (fun result (element, count) ->
        let converted = convert element in
        let previous = multiplicity equal_result converted result in
        update equal_result (converted, Z.add previous count, result))
      [] source

  (* For bounded-pool enumeration (see "compiled quantifiers" below): every element, repeated
     according to its multiplicity if `with_duplicates`, else just the distinct elements once. *)
  let to_seq ((m, with_duplicates) : ('a * Z.t) list * bool) : 'a Stdlib.Seq.t =
    if with_duplicates then
      List.to_seq m |> Stdlib.Seq.concat_map (fun (x, n) -> Stdlib.Seq.init (Z.to_int n) (fun _ -> x))
    else
      List.to_seq (List.map fst m)
end

(* ----- maps: association lists with unique keys ----- *)

module Map_ = struct
  let rec find_opt (equal_key : 'k1 -> 'k2 -> bool) (key : 'k1) = function
    | [] -> None
    | (candidate, value) :: rest ->
        if equal_key key candidate then Some value else find_opt equal_key key rest

  let get (equal_key : 'k -> 'k -> bool) ((key, map) : 'k * ('k * 'v) list) : 'v =
    match find_opt equal_key key map with
    | Some value -> value
    | None -> halt "key not found in map"

  let has_key (equal_key : 'k1 -> 'k2 -> bool)
      ((key, map) : 'k1 * ('k2 * 'v) list) : bool =
    Option.is_some (find_opt equal_key key map)

  let keys (m : ('k * 'v) list) : 'k list = List.map fst m

  let values (equal_value : 'v -> 'v -> bool) (m : ('k * 'v) list) : 'v list =
    Set.of_list equal_value (List.map snd m)

  let items (m : ('k * 'v) list) : ('k * 'v) list = m

  let cardinality (m : ('k * 'v) list) : Z.t = Z.of_int (List.length m)

  let update (equal_key : 'k -> 'k -> bool)
      ((key, value, map) : 'k * 'v * ('k * 'v) list) : ('k * 'v) list =
    if has_key equal_key (key, map) then
      List.map
        (fun (candidate, old_value) ->
          if equal_key key candidate then (candidate, value)
          else (candidate, old_value))
        map
    else
      map @ [ (key, value) ]

  let of_list (equal_key : 'k -> 'k -> bool)
      (entries : ('k * 'v) list) : ('k * 'v) list =
    List.fold_left
      (fun result (key, value) -> update equal_key (key, value, result))
      [] entries

  let merge (equal_key : 'k -> 'k -> bool)
      ((a, b) : ('k * 'v) list * ('k * 'v) list) : ('k * 'v) list =
    List.fold_left
      (fun result (key, value) -> update equal_key (key, value, result))
      a b

  let subtract (equal_key : 'k -> 'k -> bool)
      ((map, keys_to_remove) : ('k * 'v) list * 'k list) : ('k * 'v) list =
    List.filter
      (fun (key, _) -> not (Set.mem_by equal_key key keys_to_remove))
      map

  let equal (equal_key : 'k1 -> 'k2 -> bool) (equal_value : 'v1 -> 'v2 -> bool)
      ((a, b) : ('k1 * 'v1) list * ('k2 * 'v2) list) : bool =
    List.length a = List.length b
    && List.for_all
         (fun (key, value) ->
           match find_opt equal_key key b with
           | Some other -> equal_value value other
           | None -> false)
         a
end

(* ----- reference-type helpers ----- *)

let unwrap (o : 'a option) : 'a =
  match o with Some x -> x | None -> halt "value is null"

(* Reference (physical) equality for a possibly-null option-wrapped identity value or array.
   Plain `==` doesn't work here because `Some x == Some y` compares the *option boxes*, which
   are allocated afresh every time a non-null reference is wrapped — even if [x == y].
   Class/trait equality compares their shared [d_dafny_id] tokens directly in generated code. *)
let ref_eq ((a, b) : 'a option * 'a option) : bool =
  match a, b with
  | None, None -> true
  | Some x, Some y -> x == y
  | _ -> false

(* ----- printing ----- *)

let print (s : string) : unit =
  print_string s;
  flush stdout

(* ----- command line ----- *)

(* The argument vector for a Dafny `Main(args: seq<string>)`, as a seq of strings — i.e. an
   array of character arrays. Slot 0 is the program name, matching what the C#, Go, Java, and
   Python backends hand to Main. *)
let main_arguments (unicode : bool) : int array array =
  Array.map (Seq.of_string unicode) Sys.argv

(* ----- compiled quantifiers, comprehensions, and other "bounded pool" enumeration -----
   `forall`/`exists` used as an expression (not just for verification), set/map comprehensions,
   and the "ingredient" form of a `forall` *statement* (see EmitEmptyTupleList/EmitAddTupleToList)
   all need to enumerate a "bounded pool": a range of integers, `AllBooleans`, the elements of a
   set/seq/map/multiset, etc. Every one of those compiles to a plain stdlib `Stdlib.Seq.t` (a lazy
   sequence) — not to be confused with DafnyRuntime.Seq (this backend's representation of Dafny's
   own seq<T>, which is an array) — uniformly, so that CreateForeachLoop and Quantify both just
   consume `'a Stdlib.Seq.t` regardless of which kind of bound produced it. Laziness matters here mainly
   for `AllChars`, which would otherwise mean materializing a >1,000,000-element list. *)

let quantify ((elems, want_forall, pred) : 'a Stdlib.Seq.t * bool * ('a -> bool)) : bool =
  if want_forall then Stdlib.Seq.for_all pred elems else Stdlib.Seq.exists pred elems

let all_integers () : Z.t Stdlib.Seq.t =
  let rec go n () = Stdlib.Seq.Cons (n, go (if Z.gt n Z.zero then Z.neg n else Z.sub Z.one n)) in
  go Z.zero

let int_range ((lo, hi) : Z.t option * Z.t option) : Z.t Stdlib.Seq.t =
  match lo, hi with
  | Some lower, Some upper ->
      let rec go i () =
        if Z.geq i upper then Stdlib.Seq.Nil else Stdlib.Seq.Cons (i, go (Z.succ i))
      in
      go lower
  | Some lower, None ->
      let rec go i () = Stdlib.Seq.Cons (i, go (Z.succ i)) in
      go lower
  | None, Some upper ->
      let rec go i () = Stdlib.Seq.Cons (i, go (Z.pred i)) in
      go (Z.pred upper)
  | None, None -> all_integers ()

let all_booleans () : bool Stdlib.Seq.t = List.to_seq [ false; true ]

let all_chars (unicode : bool) : int Stdlib.Seq.t =
  if unicode then
    (* Unicode scalar values, excluding the surrogate range. *)
    Stdlib.Seq.filter
      (fun cp -> cp < 0xD800 || cp > 0xDFFF)
      (Stdlib.Seq.init 0x110000 (fun i -> i))
  else
    (* Legacy Dafny chars are UTF-16 code units, including surrogate code units. *)
    Stdlib.Seq.init 0x10000 (fun i -> i)
