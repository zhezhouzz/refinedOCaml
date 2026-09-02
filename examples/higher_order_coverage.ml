let[@refined.coverage
     {
       type_ =
         "f:(x:int -> {result:int | result = x}) -> x:int -> {result:int | \
          true}";
     }] apply_identity (f : int -> int) (x : int) : int =
  f x

let[@refined.coverage
     {
       type_ =
         "f:(x:int -> {result:int | result = 0}) -> x:int -> {result:int | \
          true}";
     }] bad_apply_identity (f : int -> int) (x : int) : int =
  f x

let[@refined.coverage
     {
       type_ =
         "f:(x:int -> {result:int | result = 0 || result = 1}) -> x:int -> \
          {result:int | result = 0}";
     }] same_input_is_stable (f : int -> int) (x : int) : int =
  f x - f x

(* A function witness is deterministic.  Two observations at the same input
   use the same SMT application term, so this impossible target is rejected. *)
let[@refined.coverage
     {
       type_ =
         "f:(x:int -> {result:int | result = 0 || result = 1}) -> x:int -> \
          {result:int | result = 1}";
     }] bad_same_input_is_stable (f : int -> int) (x : int) : int =
  f x - f x

(* Determinism is extensional at the observed arguments, not merely a cache of
   identical syntax: [x] and [x + 0] denote the same input. *)
let[@refined.coverage
     {
       type_ =
         "f:(x:int -> {result:int | result = 0 || result = 1}) -> x:int -> \
          {result:int | result = 0}";
     }] equal_inputs_are_stable (f : int -> int) (x : int) : int =
  f x - f (x + 0)

let[@refined.coverage
     {
       type_ =
         "f:(x:int -> {result:int | result = 0 || result = 1}) -> x:int -> \
          {result:int | result = 1}";
     }] bad_equal_inputs_are_stable (f : int -> int) (x : int) : int =
  f x - f (x + 0)

(* Function-valued coverage is interpreted pointwise: [x] is a universal
   observation argument, while the original [unit] input remains an
   existential generator witness. *)
let[@refined.coverage
     { type_ = "unit:unit -> x:int -> {result:int | result = x}" }] make_identity
    (unit : unit) : int -> int =
 fun x -> x

let[@refined.coverage
     { type_ = "unit:unit -> x:int -> {result:int | result = x}" }] bad_make_identity
    (unit : unit) : int -> int =
 fun x -> x + 1
