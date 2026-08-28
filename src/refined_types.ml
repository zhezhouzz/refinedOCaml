module Source_span = Source_span

type mode = Over | Under
type verdict = Valid | Invalid of string | Unknown of string

type proof_artifact = {
  lemma_name : string;
  vc_digest : string;
  solver : string;
  timeout_seconds : int;
  trusted_axioms : string list;
  checked_dependencies : string list;
}

type obligation = {
  name : string;
  mode : mode;
  location : Source_span.t;
  smt : string;
  trusted_axioms : string list;
  checked_lemmas : string list;
  proof_artifacts : proof_artifact list;
  ghost_instantiations : string list;
}

let mode_name = function Over -> "over" | Under -> "coverage"
