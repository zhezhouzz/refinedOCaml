type chain = End | Link of int ref * chain

let[@refined.over
     {
       type_ = "x:int -> chain";
       result_references = [ ("Link.0", "value = x") ];
     }] recursive_ownership (x : int) : chain =
  Link (ref x, End)
