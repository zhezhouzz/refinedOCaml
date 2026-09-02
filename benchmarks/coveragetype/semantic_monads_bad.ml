(* Mutation controls for the monadic benchmark family. *)

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {result:int | result = 1 || result = 2}";
       witness_relation = "result = 1";
     }] monad_union_branch_mutation (unit_value : unit) : int =
  let _unused_unit = unit_value in
  1

let[@refined.coverage
     { type_ = "value:int -> int"; witness_relation = "result = value + 1" }] monad_return_relation_mutation
    (value : int) : int =
  value

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {result:int | result >= 0}";
       witness_relation = "size = 0 && result = size";
     }] monad_recursive_constructor_mutation (size : int) : int =
  size
