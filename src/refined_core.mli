type mode = Over | Under
type verdict = Valid | Invalid of string | Unknown of string

type obligation = {
  name : string;
  mode : mode;
  location : Location.t;
  smt : string;
  trusted_axioms : string list;
}

val obligations_of_cmt : string -> obligation list

val obligations_of_cmt_with_theories :
  theories:string list -> string -> obligation list

val write_rmi : cmti:string -> output:string -> unit
val solve : obligation -> verdict
val mode_name : mode -> string
