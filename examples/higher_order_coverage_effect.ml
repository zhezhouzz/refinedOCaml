exception Negative_callback

let[@refined.over
     {
       type_ =
         "f:(x:{x:int | x >= 0} -> {result:int | result > x}) -> x:{x:int | x \
          >= 0} -> {result:int | result > x}";
     }] apply_positive (f : int -> int) (x : int) : int =
  f x

(* The callback is a closure witness.  Its exceptional branch is unreachable
   on the callback domain required by [apply_positive]. *)
let[@refined.coverage { type_ = "unit:unit -> {result:int | result = 1}" }] effectful_callback
    (unit : unit) : int =
  apply_positive (fun y -> if y >= 0 then y + 1 else raise Negative_callback) 0

(* The target value is reachable operationally, but the callback violates the
   higher-order safety contract, so coverage must reject it. *)
let[@refined.coverage { type_ = "unit:unit -> {result:int | result = -1}" }] bad_effectful_callback
    (unit : unit) : int =
  apply_positive (fun y -> if y >= 0 then y - 1 else raise Negative_callback) 0

(* Returned functions are covered pointwise.  The synthetic [x] observation
   is universal and its refinement guards the coverage obligation. *)
let[@refined.coverage
     { type_ = "unit:unit -> x:{x:int | x >= 0} -> {result:int | result = x}" }] make_effectful_identity
    (unit : unit) : int -> int =
 fun x -> if x >= 0 then x else raise Negative_callback

let[@refined.coverage
     { type_ = "unit:unit -> x:{x:int | x >= 0} -> {result:int | result = x}" }] bad_make_effectful_identity
    (unit : unit) : int -> int =
 fun x -> if x >= 0 then x + 1 else raise Negative_callback

let[@refined.coverage
     {
       type_ =
         "minimum:int -> x:{x:int | x >= minimum} -> {result:int | result = x}";
       universals = [ "minimum" ];
     }] make_bounded_effectful_identity (minimum : int) : int -> int =
 fun x -> if x >= minimum then x else raise Negative_callback

let[@refined.coverage
     {
       type_ =
         "minimum:int -> x:{x:int | x >= minimum} -> {result:int | result = x}";
       universals = [ "minimum" ];
     }] bad_make_bounded_effectful_identity (minimum : int) : int -> int =
 fun x -> if x >= minimum then x + 1 else raise Negative_callback
