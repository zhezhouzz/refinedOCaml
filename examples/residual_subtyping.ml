let[@refined.over
     { type_ = "offset:int -> x:int -> {result:int | result = offset + x}" }] add
    (offset : int) (x : int) : int =
  offset + x

let[@refined.over
     {
       type_ =
         "f:(x:int -> {result:int | result = x + 2}) -> x:int -> {result:int | \
          result = x + 2}";
     }] apply_add_two (f : int -> int) (x : int) : int =
  f x

(* Applying [add] to 2 produces the dependent residual type
   [x:int -> {result | result = 2 + x}]. *)
let[@refined.over { type_ = "x:int -> {result:int | result = x + 2}" }] use_residual
    (x : int) : int =
  let add_two = add 2 in
  apply_add_two add_two x

let[@refined.over { type_ = "x:int -> {result:int | result = x + 2}" }] use_wrong_residual
    (x : int) : int =
  let add_three = add 3 in
  apply_add_two add_three x
