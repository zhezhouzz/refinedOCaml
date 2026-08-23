let[@refined.over { pre = "x >= 0"; post = "result > x" }] bad_succ (x : int) :
    int =
  x - 1

(* The image of x + 2 for x >= 0 does not cover result = 1. *)
let[@refined.under { pre = "x >= 0"; post = "result >= 1" }] misses_one
    (x : int) : int =
  x + 2
