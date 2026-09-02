let[@refined.coverage
     {
       type_ = "x:int -> {result:int | result >= 1}";
       ghosts = [ ("inverse", "int") ];
       witness_relation = "inverse = result && x = inverse";
     }] wrong_ghost_successor (x : int) : int =
  x + 1

let[@refined.coverage { type_ = "x:int -> int"; witness_relation = "false" }] empty_relation
    (x : int) : int =
  x
