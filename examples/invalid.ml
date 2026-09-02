let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] bad_succ
    (x : int) : int =
  x - 1

(* The image of x + 2 for x >= 0 does not cover result = 1. *)
let[@refined.coverage
     { type_ = "x:{x:int | x >= 0} -> {result:int | result >= 1}" }] misses_one
    (x : int) : int =
  x + 2
