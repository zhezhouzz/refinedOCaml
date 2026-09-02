type chain = End | Link of int ref * chain

let[@refined.over
     {
       type_ = "_seed:int -> chain";
       result_recursive = true;
       result_region = "nonnegative_chain";
       result_references = [ ("Link.0", "value >= 0") ];
       result_reference_permissions = [ ("Link.0", "transfer") ];
     }] empty_chain (_seed : int) : chain =
  End

let[@refined.over
     {
       type_ = "x:int -> tail:{tail:chain | x >= 0} -> chain";
       result_recursive = true;
       result_region = "nonnegative_chain";
       requires_regions = [ ("tail", "nonnegative_chain") ];
       result_references = [ ("Link.0", "value >= 0") ];
       result_reference_permissions = [ ("Link.0", "transfer") ];
     }] make_link (x : int) (tail : chain) : chain =
  Link (ref x, tail)

let[@refined.over { type_ = "x:{x:int | x >= 0} -> int" }] read_new_link
    (x : int) : int =
  match make_link x End with End -> 0 | Link (cell, _tail) -> !cell

let[@refined.over
     {
       type_ = "value:chain -> int";
       requires_regions = [ ("value", "nonnegative_chain") ];
       consumes_regions = [ "value" ];
     }] consume_chain (value : chain) : int =
  let _discarded = value in
  0

let[@refined.over
     {
       type_ = "value:chain -> {result:int | result >= 0}";
       requires_regions = [ ("value", "nonnegative_chain") ];
       consumes_regions = [ "value" ];
     }] head_nonnegative (value : chain) : int =
  match value with End -> 0 | Link (cell, _tail) -> !cell

let[@refined.over
     {
       type_ = "cell:int ref -> int ref * int";
       result_references = [ ("0", "identity = cell") ];
       result_reference_permissions = [ ("0", "borrow") ];
     }] borrow_ref (cell : int ref) : int ref * int =
  (cell, 0)

let[@refined.over { type_ = "cell:int ref -> {result:bool | result}" }] borrowed_identity
    (cell : int ref) : bool =
  match borrow_ref cell with borrowed, _ -> borrowed == cell
