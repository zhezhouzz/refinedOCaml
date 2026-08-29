type chain = End | Link of int ref * chain

let[@refined.over
     {
       pre = "true";
       post = "true";
       result_recursive = true;
       result_references = [ ("Link.0", "value = x") ];
       result_reference_permissions = [ ("Link.0", "transfer") ];
     }]
   [@refined.coverage
     {
       pre = "true";
       post = "result <> End";
       result_recursive = true;
       result_references = [ ("Link.0", "true") ];
       result_reference_permissions = [ ("Link.0", "transfer") ];
       witness_relation =
         "x = result_value_Link_0 && result = Link(result_identity_Link_0, \
          tail)";
     }] make_link (x : int) (tail : chain) : chain =
  Link (ref x, tail)

let[@refined.over { pre = "true"; post = "result = 0 || result = x" }] read_new_link
    (x : int) (tail : chain) : int =
  match make_link x tail with End -> 0 | Link (cell, _tail) -> !cell

let[@refined.over
     {
       pre = "true";
       post = "true";
       result_references = [ ("0", "identity = cell") ];
       result_reference_permissions = [ ("0", "borrow") ];
     }] borrow_ref (cell : int ref) : int ref * int =
  (cell, 0)

let[@refined.over { pre = "true"; post = "result" }] borrowed_identity
    (cell : int ref) : bool =
  match borrow_ref cell with borrowed, _ -> borrowed == cell
