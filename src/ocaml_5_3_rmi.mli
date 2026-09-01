open Refined_ir

val write_rmi :
  ensure_supported_version:(unit -> unit) ->
  new_registry:(unit -> Typed_core.registry) ->
  register_signature_theories:
    (Typed_core.registry -> root:string -> Typedtree.signature -> unit) ->
  verify:
    (Typed_core.registry ->
    Typed_core.axiom list ->
    Refined_types.proof_artifact list) ->
  cmti:string ->
  output:string ->
  unit

val load_rmi_into :
  Typed_core.registry -> Cmt_format.cmt_infos -> string -> unit
