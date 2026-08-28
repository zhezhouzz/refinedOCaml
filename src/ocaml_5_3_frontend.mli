open Refined_ir

val supported_ocaml_version : string
val ensure_supported_version : unit -> unit

val write_rmi :
  verify:
    (Typed_core.registry ->
    Typed_core.axiom list ->
    Refined_types.proof_artifact list) ->
  cmti:string ->
  output:string ->
  unit

val program_of_cmt : theories:string list -> string -> Typed_core.program
