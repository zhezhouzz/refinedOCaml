let[@refined.coverage
     {
       pre = "true";
       post = "result >= 1";
       ghosts = [ ("inverse", "int") ];
       witness_relation = "inverse = result && x = inverse";
     }] wrong_ghost_successor (x : int) : int =
  x + 1

let[@refined.coverage
     { pre = "true"; post = "true"; witness_relation = "false" }] empty_relation
    (x : int) : int =
  x
