open Refined_ir

type bundle = {
  unit_name : string;
  interface_digest : string option;
  artifacts : Refined_types.proof_artifact list;
}

val sha256 : string -> string
val canonical_statement : Typed_core.axiom -> string
val statement_digest : Typed_core.axiom -> string
val write : path:string -> bundle -> unit
val read : string -> bundle
val validate : bundle -> (unit, string) result
