(* Mutation control: the application branch is required to cover positive
   application counts. *)

let[@refined.coverage
     {
       type_ = "apps:{apps:int | apps >= 0} -> {result:int | result >= 0}";
       witness_relation = "apps = 0 && result = apps";
     }] stlc_application_mutation (apps : int) : int =
  apps
