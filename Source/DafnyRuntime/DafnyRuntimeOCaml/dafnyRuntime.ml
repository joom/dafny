(* Dafny runtime support for the OCaml backend.

   Design (see Docs/Compilation/OCaml.md for the rationale):
   - Dafny's `int` and all bit-vector/native integer types are represented
     uniformly as Zarith's arbitrary-precision [Z.t].
   - Dafny's `real` is represented as Zarith's arbitrary-precision rational [Q.t].
   - Dafny's `char` is represented as a plain OCaml [int] holding a Unicode code point.
   - `seq<T>` and `array<T>` are both represented as OCaml ['a array] (a seq is
     conceptually immutable; the compiler only mutates arrays that came from
     `array<T>`, and always copies when a seq is derived from one).
   - `set<T>` is a deduplicated ['a list].
   - `multiset<T>` is a ['a * Z.t) list] of (element, multiplicity) pairs, kept free
     of zero-multiplicity entries.
   - `map<K, V>` is a ['(K * V) list] association list, kept free of duplicate keys.
   - Class (reference) types are represented as ['a option], with [None] for `null`.

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

(* ----- integers ----- *)

module Int = struct
  type t = Z.t

  let zero = Z.zero
  let one = Z.one
  let of_int = Z.of_int
  let of_string = Z.of_string
  let to_int = Z.to_int
  let to_string = Z.to_string
  let equal = Z.equal
  let compare = Z.compare
  let succ = Z.succ
  let pred = Z.pred
  let neg = Z.neg
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

  (* Dafny characters are Unicode code points, represented as plain OCaml ints; these let
     char +/- int arithmetic reuse the same DafnyRuntime.Int.add/sub call sites as numbers. *)
  let add_char ((a, b) : int * t) : int = a + Z.to_int b
  let sub_char ((a, b) : int * t) : int = a - Z.to_int b

  let truncate (width : int) (signed : bool) (x : t) : t =
    let m = Z.shift_left Z.one width in
    let r = Z.erem x m in
    if signed && Z.geq r (Z.shift_left Z.one (width - 1)) then Z.sub r m else r
end

(* ----- characters (Unicode code points, represented as native ints) ----- *)

module Char_ = struct
  let utf8_of_code_point (buf : Buffer.t) (cp : int) : unit =
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
end

(* ----- sequences (also used for strings and, when mutated, arrays) ----- *)

module Seq = struct
  let length (s : 'a array) : Z.t = Z.of_int (Array.length s)

  let empty () : 'a array = [||]

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

  let contains ((s, x) : 'a array * 'a) : bool = Array.exists (( = ) x) s

  let is_prefix ((a, b) : 'a array * 'a array) : bool =
    Array.length a <= Array.length b && Array.sub b 0 (Array.length a) = a

  let is_proper_prefix ((a, b) : 'a array * 'a array) : bool =
    Array.length a < Array.length b && is_prefix (a, b)

  let of_string (s : string) : int array =
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
      out := cp :: !out;
      i := !i + len
    done;
    Array.of_list (List.rev !out)

  let string_of_chars (s : int array) : string =
    let buf = Buffer.create (Array.length s) in
    Array.iter (Char_.utf8_of_code_point buf) s;
    Buffer.contents buf
end

(* ----- sets ----- *)

module Set = struct
  let of_list (l : 'a list) : 'a list =
    List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] l

  let of_seq (s : 'a array) : 'a list = of_list (Array.to_list s)

  let cardinality (s : 'a list) : Z.t = Z.of_int (List.length s)

  let mem ((x, s) : 'a * 'a list) : bool = List.mem x s

  let union ((a, b) : 'a list * 'a list) : 'a list = of_list (a @ b)

  let intersect ((a, b) : 'a list * 'a list) : 'a list =
    List.filter (fun x -> List.mem x b) a

  let difference ((a, b) : 'a list * 'a list) : 'a list =
    List.filter (fun x -> not (List.mem x b)) a

  let is_subset ((a, b) : 'a list * 'a list) : bool =
    List.for_all (fun x -> List.mem x b) a

  let is_proper_subset ((a, b) : 'a list * 'a list) : bool =
    is_subset (a, b) && List.length a < List.length b

  let is_disjoint ((a, b) : 'a list * 'a list) : bool =
    List.for_all (fun x -> not (List.mem x b)) a

  let equal ((a, b) : 'a list * 'a list) : bool = is_subset (a, b) && is_subset (b, a)
end

(* ----- multisets: (element, positive multiplicity) pairs ----- *)

module Multiset = struct
  let normalize (l : ('a * Z.t) list) : ('a * Z.t) list =
    List.filter (fun (_, n) -> Z.gt n Z.zero) l

  let of_seq (s : 'a array) : ('a * Z.t) list =
    let add acc x =
      match List.assoc_opt x acc with
      | Some n -> (x, Z.add n Z.one) :: List.remove_assoc x acc
      | None -> (x, Z.one) :: acc
    in
    Array.fold_left add [] s

  let of_set (s : 'a list) : ('a * Z.t) list = List.map (fun x -> (x, Z.one)) s

  let multiplicity (x : 'a) (m : ('a * Z.t) list) : Z.t =
    match List.assoc_opt x m with Some n -> n | None -> Z.zero

  let update ((x, n, m) : 'a * Z.t * ('a * Z.t) list) : ('a * Z.t) list =
    normalize ((x, n) :: List.remove_assoc x m)

  let cardinality (m : ('a * Z.t) list) : Z.t =
    List.fold_left (fun acc (_, n) -> Z.add acc n) Z.zero m

  let all_keys (a : ('a * Z.t) list) (b : ('a * Z.t) list) : 'a list =
    Set.of_list (List.map fst a @ List.map fst b)

  let union ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : ('a * Z.t) list =
    List.map (fun x -> (x, Z.add (multiplicity x a) (multiplicity x b))) (all_keys a b)

  let intersect ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : ('a * Z.t) list =
    normalize (List.map (fun x -> (x, Z.min (multiplicity x a) (multiplicity x b))) (all_keys a b))

  let difference ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : ('a * Z.t) list =
    normalize (List.map (fun x -> (x, Z.sub (multiplicity x a) (multiplicity x b))) (all_keys a b))

  let is_subset ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : bool =
    List.for_all (fun x -> Z.leq (multiplicity x a) (multiplicity x b)) (all_keys a b)

  let is_proper_subset ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : bool =
    is_subset (a, b) && cardinality a < cardinality b

  let is_disjoint ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : bool =
    List.for_all (fun x -> Z.equal (multiplicity x a) Z.zero || Z.equal (multiplicity x b) Z.zero) (all_keys a b)

  let equal ((a, b) : ('a * Z.t) list * ('a * Z.t) list) : bool = is_subset (a, b) && is_subset (b, a)

  let mem ((x, m) : 'a * ('a * Z.t) list) : bool = Z.gt (multiplicity x m) Z.zero
end

(* ----- maps: association lists with unique keys ----- *)

module Map_ = struct
  let get ((k, m) : 'k * ('k * 'v) list) : 'v = List.assoc k m

  let has_key ((k, m) : 'k * ('k * 'v) list) : bool = List.mem_assoc k m

  let keys (m : ('k * 'v) list) : 'k list = List.map fst m

  let values (m : ('k * 'v) list) : 'v list = List.map snd m

  let items (m : ('k * 'v) list) : ('k * 'v) list = m

  let cardinality (m : ('k * 'v) list) : Z.t = Z.of_int (List.length m)

  let update ((k, v, m) : 'k * 'v * ('k * 'v) list) : ('k * 'v) list =
    (k, v) :: List.remove_assoc k m

  let merge ((a, b) : ('k * 'v) list * ('k * 'v) list) : ('k * 'v) list =
    List.fold_left (fun acc (k, v) -> update (k, v, acc)) a b

  let subtract ((m, keysToRemove) : ('k * 'v) list * 'k list) : ('k * 'v) list =
    List.filter (fun (k, _) -> not (List.mem k keysToRemove)) m

  let equal ((a, b) : ('k * 'v) list * ('k * 'v) list) : bool =
    List.length a = List.length b
    && List.for_all (fun (k, v) -> match List.assoc_opt k b with Some v' -> v = v' | None -> false) a
end

(* ----- reference-type helpers ----- *)

let unwrap (o : 'a option) : 'a =
  match o with Some x -> x | None -> halt "value is null"

(* ----- printing ----- *)

let print (s : string) : unit =
  print_string s;
  flush stdout
