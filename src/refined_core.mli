open Refined_ir
include module type of Refined_types

val obligations_of_cmt : string -> obligation list

val obligations_of_cmt_with_theories :
  theories:string list -> string -> obligation list

val proof_digest : string -> string
val write_rmi : cmti:string -> output:string -> unit
val replay_proof : string -> int
val solve : obligation -> verdict
