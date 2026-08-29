type chain = End | Link of int ref * chain

let[@refined.over
     {
       pre = "true";
       post = "true";
       result_recursive = true;
       result_region = "linear_chain";
       result_references = [ ("Link.0", "true") ];
       result_reference_permissions = [ ("Link.0", "transfer") ];
     }] empty_chain (_seed : int) : chain =
  End

let[@refined.over
     {
       pre = "true";
       post = "true";
       requires_regions = [ ("value", "linear_chain") ];
       consumes_regions = [ "value" ];
     }] consume_chain (_value : chain) : int =
  0

let[@refined.over { pre = "true"; post = "true" }] double_consume (_seed : int)
    : int =
  let value = empty_chain 0 in
  let _first = consume_chain value in
  consume_chain value
