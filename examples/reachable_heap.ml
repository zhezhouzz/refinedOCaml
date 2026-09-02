type box = Box of int ref
type maybe_ref = NoRef | SomeRef of int ref

let[@refined.over
     {
       type_ = "x:int -> flag:bool -> int ref * bool ref";
       result_references = [ ("0", "value = x"); ("1", "value = flag") ];
       result_fresh_references = [ "0"; "1" ];
     }]
   [@refined.coverage
     {
       type_ = "x:int -> flag:bool -> int ref * bool ref";
       result_references = [ ("0", "true"); ("1", "true") ];
       result_fresh_references = [ "0"; "1" ];
       witness_relation = "x = result_value_0 && flag = result_value_1";
     }] make_pair (x : int) (flag : bool) : int ref * bool ref =
  (ref x, ref flag)

let[@refined.over { type_ = "x:int -> flag:bool -> {result:bool | result}" }]
   [@refined.coverage
     {
       type_ = "x:int -> flag:bool -> {result:bool | result}";
       witness_relation = "x = 1 && flag";
     }] read_pair (x : int) (flag : bool) : bool =
  match make_pair x flag with left, right -> !left = x && !right = flag

let[@refined.over
     {
       type_ = "x:int -> box * int";
       result_references = [ ("0.Box.0", "value = x") ];
       result_fresh_references = [ "0.Box.0" ];
     }] make_nested_box (x : int) : box * int =
  (Box (ref x), x)

let[@refined.over { type_ = "x:int -> {result:int | result = x}" }] read_nested_box
    (x : int) : int =
  match make_nested_box x with Box cell, _ -> !cell

let[@refined.over
     {
       type_ = "x:int -> maybe_ref";
       result_references = [ ("SomeRef.0", "value = x") ];
       result_fresh_references = [ "SomeRef.0" ];
     }] make_some (x : int) : maybe_ref =
  SomeRef (ref x)

let[@refined.over
     { type_ = "x:int -> {result:int | result = 0 || result = x}" }] read_some
    (x : int) : int =
  match make_some x with NoRef -> 0 | SomeRef cell -> !cell
