(* Mutation control for the inverse rank witness used by LeftistHeap. *)
let[@refined.coverage
     {
       type_ = "rank:int -> {result:int | true}";
       witness_relation = "rank = result";
     }] generate_bad_rank (rank : int) : int =
  rank + 1
