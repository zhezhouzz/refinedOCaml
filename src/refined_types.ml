module Source_span = Source_span

type mode = Over | Under
type verdict = Valid | Invalid of string | Unknown of string

type obligation = {
  name : string;
  mode : mode;
  location : Source_span.t;
  smt : string;
  trusted_axioms : string list;
  ghost_instantiations : string list;
}

let mode_name = function Over -> "over" | Under -> "coverage"
