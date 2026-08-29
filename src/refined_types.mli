module Source_span = Source_span

type mode = Over | Under
type verdict = Valid | Invalid of string | Unknown of string

type proof_artifact = {
  artifact_version : int;
  lemma_name : string;
  statement : string;
  statement_digest : string;
  digest_algorithm : string;
  vc_digest : string;
  vc_smt : string;
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

val mode_name : mode -> string
