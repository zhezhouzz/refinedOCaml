type nat = Z | S of nat
type point = { x : int; y : int }

let[@refined.over { type_ = "x:{v:int | v >= 0} -> {v:int | v > x}" }] succ
    (x : int) : int =
  x + 1

(* Every integer result >= 1 has the witness x = result - 1, with x >= 0. *)
let[@refined.coverage
     {
       type_ = "x:{v:int | v >= 0} -> {v:int | v >= 1}";
       witnesses = [ ("x", "result - 1") ];
     }] positive_range (x : int) : int =
  x + 1

let[@refined.over { type_ = "n:nat -> {v:bool | (v = true) = (n = Z)}" }] is_zero
    (n : nat) : bool =
  match n with Z -> true | S _ -> false

(* Under-refinement: identity covers the entire uninterpreted Nat carrier. *)
let[@refined.coverage { type_ = "n:nat -> nat" }] id_nat (n : nat) : nat = n

let[@refined.over
     { type_ = "x:int -> y:int -> {v:point | (v.x = x) && (v.y = y)}" }] make_point
    (x : int) (y : int) : point =
  { x; y }

let[@refined.over
     { type_ = "x:int -> y:{v:int | v >= x} -> {v:int | v = x + y}" }] add
    (x : int) (y : int) : int =
  x + y

let[@refined.over { type_ = "y:{v:int | v >= 3} -> {v:int | v = y + 3}" }] add_three
    (y : int) : int =
  let add_three = add 3 in
  add_three y

let[@refined.over
     { type_ = "flag:bool -> y:{v:int | v >= 4} -> {v:int | v >= y + 3}" }] branch_partial
    (flag : bool) (y : int) : int =
  let add_some = if flag then add 3 else add 4 in
  add_some y

let[@refined.over { type_ = "y:{v:int | v >= 3} -> {v:int | v = (2 * y) + 7}" }] reuse_partial
    (y : int) : int =
  let add_three = add 3 in
  add_three y + add_three (y + 1)
