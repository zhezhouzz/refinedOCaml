type chain = End | Link of int ref * chain

let[@refined.over
     {
       type_ = "_seed:int -> chain";
       result_recursive = true;
       result_region = "alias_chain";
       result_references = [ ("Link.0", "true") ];
       result_reference_permissions = [ ("Link.0", "transfer") ];
     }] empty_chain (_seed : int) : chain =
  End

let[@refined.over
     {
       type_ = "_value:chain -> int";
       requires_regions = [ ("value", "alias_chain") ];
       consumes_regions = [ "value" ];
     }] consume_chain (_value : chain) : int =
  0

let[@refined.over { type_ = "_seed:int -> int" }] consume_borrowed (_seed : int)
    : int =
  let value = empty_chain 0 in
  let _alias = value in
  consume_chain value
