type mode = Over | Under

type verdict =
  | Valid
  | Invalid of string
  | Unknown of string

type obligation = {
  name : string;
  mode : mode;
  location : Location.t;
  smt : string;
}

val obligations_of_file : string -> obligation list
val solve : obligation -> verdict
val mode_name : mode -> string

