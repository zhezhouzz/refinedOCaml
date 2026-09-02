(* Mutation control shared by both queue ports: keeping only the empty-front
   branch cannot cover queues with positive front length. *)

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {result:int | result >= 0}";
       witness_relation = "size = 0 && result = size";
     }] queue_nonempty_branch_mutation (size : int) : int =
  size
