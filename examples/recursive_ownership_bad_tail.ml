type chain = End | Link of int ref * chain

let[@refined.over
     {
       type_ = "tail:chain -> chain";
       result_recursive = true;
       result_region = "bad_tail_chain";
       result_references = [ ("Link.0", "true") ];
       result_reference_permissions = [ ("Link.0", "transfer") ];
     }] bad_tail (tail : chain) : chain =
  Link (ref 0, tail)
