(* Mutation control for the recursive tree families: a leaf-only generator
   cannot cover positive depths. *)

let[@refined.coverage
     {
       type_ = "depth:{depth:int | depth >= 0} -> {result:int | result >= 0}";
       witness_relation = "depth = 0 && result = depth";
     }] tree_node_branch_mutation (depth : int) : int =
  depth
