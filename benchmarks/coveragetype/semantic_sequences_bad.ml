(* Mutation controls for the list and stream families. Each implementation
   models a generator whose recursive constructor branch was deleted. *)

let[@refined.coverage
     {
       type_ = "depth:{depth:int | depth >= 0} -> {result:int | result >= 0}";
       witness_relation = "depth = 0 && result = depth";
     }] list_constructor_mutation (depth : int) : int =
  depth

let[@refined.coverage
     {
       type_ = "depth:{depth:int | depth >= 0} -> {result:int | result >= 0}";
       witness_relation = "depth = 0 && result = depth";
     }] stream_constructor_mutation (depth : int) : int =
  depth
