open Refined_ir

val typed_register_theories : Typed_core.registry -> Typedtree.structure -> unit

val typed_register_signature_theories :
  Typed_core.registry -> root:string -> Typedtree.signature -> unit
