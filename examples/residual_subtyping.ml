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

(* This is the curried form of a joint precondition [y > x].  Supplying [x]
   must retain it in the residual function's domain as [y > captured_x]. *)
let[@refined.over
     { type_ = "x:int -> y:{y:int | y > x} -> {result:int | result = y - x}" }] difference
    (x : int) (y : int) : int =
  y - x

let[@refined.over
     {
       type_ =
         "f:(y:{y:int | y > 3} -> {result:int | result = y - 3}) -> y:{y:int | \
          y > 3} -> {result:int | result = y - 3}";
     }] apply_after_three (f : int -> int) (y : int) : int =
  f y

let[@refined.over
     { type_ = "y:{y:int | y > 3} -> {result:int | result = y - 3}" }] use_dependent_residual
    (y : int) : int =
  let from_three = difference 3 in
  apply_after_three from_three y

let[@refined.over
     { type_ = "y:{y:int | y > 3} -> {result:int | result = y - 4}" }] use_wrong_dependent_residual
    (y : int) : int =
  let from_three = difference 3 in
  apply_after_three from_three y

let[@refined.over
     {
       type_ =
         "f:(y:int -> {result:int | result = y - 3}) -> y:int -> {result:int | \
          result = y - 3}";
     }] apply_at_any_int (f : int -> int) (y : int) : int =
  f y

(* [difference 3] is not defined by its refinement contract at [y <= 3], so
   it cannot be widened to the all-integer callback domain. *)
let[@refined.over { type_ = "y:int -> {result:int | result = y - 3}" }] use_dependent_residual_outside_domain
    (y : int) : int =
  let from_three = difference 3 in
  apply_at_any_int from_three y
