let[@refined.over { pre = "true"; post = "result = (left == right)" }] same_ref
    (left : int ref) (right : int ref) : bool =
  left == right

let[@refined.over { pre = "true"; post = "result" }] distinct_allocations
    (_unit : unit) : bool =
  let left = ref 0 in
  let right = ref 0 in
  left != right

let[@refined.over
     {
       pre = "true";
       requires_state = [ ("cell", "value = 7") ];
       post = "result = cell";
       result_state = "value = 7";
     }]
   [@refined.coverage
     {
       pre = "true";
       post = "true";
       result_state = "value = 7";
       witness_relation = "result = cell && old_cell = 7";
     }] return_alias (cell : int ref) : int ref =
  cell

let[@refined.over
     {
       pre = "true";
       requires_state = [ ("cell", "value = 7") ];
       post = "result";
     }]
   [@refined.coverage
     { pre = "true"; post = "result"; witness_relation = "old_cell = 7" }] alias_wrapper
    (cell : int ref) : bool =
  let alias = return_alias cell in
  alias == cell && !alias = 7

let[@refined.over
     {
       pre = "true";
       post = "true";
       result_state = "value = x";
       result_fresh = true;
     }]
   [@refined.coverage
     {
       pre = "true";
       post = "true";
       result_state = "true";
       result_fresh = true;
       witness_relation = "x = result_value";
     }] make_ref (x : int) : int ref =
  ref x

let[@refined.over { pre = "true"; post = "result = x" }]
   [@refined.coverage
     { pre = "true"; post = "result >= 0"; witness_relation = "x = result" }] read_fresh
    (x : int) : int =
  let cell = make_ref x in
  !cell

let[@refined.over { pre = "true"; post = "result" }] two_fresh_refs
    (_unit : unit) : bool =
  let left = make_ref 1 in
  let right = make_ref 2 in
  left != right
