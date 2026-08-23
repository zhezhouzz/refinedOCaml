type nat = Z | S of nat
type point = { x : int; y : int }

let[@refined.over { pre = "x >= 0"; post = "result > x" }] succ (x : int) : int
    =
  x + 1

(* Every integer result >= 1 has the witness x = result - 1, with x >= 0. *)
let[@refined.under { pre = "x >= 0"; post = "result >= 1" }] positive_range
    (x : int) : int =
  x + 1

let[@refined.over { pre = "true"; post = "(result = true) = (n = Z)" }] is_zero
    (n : nat) : bool =
  match n with Z -> true | S _ -> false

(* Under-refinement: identity covers the entire uninterpreted Nat carrier. *)
let[@refined.under { pre = "true"; post = "true" }] id_nat (n : nat) : nat = n

let[@refined.over { pre = "true"; post = "(result.x = x) && (result.y = y)" }] make_point
    (x : int) (y : int) : point =
  { x; y }
