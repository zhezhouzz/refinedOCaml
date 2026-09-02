(* [size] is an over/universal index.  The returned generator is checked under
   pointwise coverage, so its [unit] argument is a universal observation while
   any remaining unmarked top-level parameters would be existential witnesses. *)
let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> unit:unit -> {result:int | result = \
          size}";
       universals = [ "size" ];
     }] indexed_generator (size : int) : unit -> int =
 fun _unit -> size

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> unit:unit -> {result:int | result = \
          size}";
       universals = [ "size" ];
     }] bad_indexed_generator (size : int) : unit -> int =
 fun _unit -> size + 1

(* A one-marker choice is a typed havoc source.  It models upstream generator
   primitives such as [int_gen ()] without a target seed parameter. *)
let[@refined.choose] arbitrary_int (_unit : unit) : int = 0

let[@refined.coverage { type_ = "unit:unit -> {result:int | true}" }] any_int
    (unit : unit) : int =
  arbitrary_int unit

let[@refined.over { type_ = "unit:unit -> {result:int | result >= 0}" }] bad_any_int_safety
    (unit : unit) : int =
  arbitrary_int unit
