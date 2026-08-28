open Refined_ir

val obligations_of_cmt : string -> Refined_types.obligation list

val obligations_of_cmt_with_theories :
  theories:string list -> string -> Refined_types.obligation list

val lemma_obligations :
  Typed_core.registry -> Typed_core.axiom list -> Refined_types.obligation list
