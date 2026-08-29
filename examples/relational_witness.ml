let[@refined.coverage
     {
       pre = "true";
       post = "result >= 0";
       witness_relation = "x = result || x = 0 - result";
     }] absolute (x : int) : int =
  if x >= 0 then x else 0 - x

let[@refined.coverage
     { pre = "true"; post = "result >= 0"; witness_relation = "x = result" }] absolute_wrapper
    (x : int) : int =
  absolute x

let[@refined.coverage
     {
       pre = "true";
       post = "result >= 1";
       ghosts = [ ("inverse", "int") ];
       witness_relation = "inverse = result - 1 && x = inverse";
     }] ghost_successor (x : int) : int =
  x + 1

let[@refined.coverage
     { pre = "true"; post = "result >= 1"; witness_relation = "x = result - 1" }] ghost_wrapper
    (x : int) : int =
  ghost_successor x

let[@refined.coverage
     {
       pre = "true";
       post = "result >= 1";
       state = [ ("cell", "value = result") ];
       witness_relation = "old_cell = result - 1";
     }] relational_bump (cell : int ref) : int =
  cell := !cell + 1;
  !cell

let[@refined.coverage
     {
       pre = "true";
       post = "result >= 1";
       state = [ ("cell", "value = result") ];
       witness_relation = "old_cell = result - 1";
     }] relational_bump_wrapper (cell : int ref) : int =
  relational_bump cell
