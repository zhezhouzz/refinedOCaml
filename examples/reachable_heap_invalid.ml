type box = Box of int ref

let[@refined.over
     {
       type_ = "x:int -> box";
       result_references = [ ("Box.0", "value = x + 1") ];
       result_fresh_references = [ "Box.0" ];
     }] wrong_content (x : int) : box =
  Box (ref x)

let[@refined.over
     {
       type_ = "x:int -> int ref * int ref";
       result_references = [ ("0", "value = x"); ("1", "value = x") ];
       result_fresh_references = [ "0"; "1" ];
     }] falsely_distinct_pair (x : int) : int ref * int ref =
  let shared = ref x in
  (shared, shared)
