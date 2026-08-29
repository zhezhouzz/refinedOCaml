open Refined_ir
include Refined_types

let obligations_of_cmt = Vc_backend.obligations_of_cmt

let obligations_of_cmt_with_theories =
  Vc_backend.obligations_of_cmt_with_theories

let proof_digest = Proof_artifact_io.sha256

let write_rmi ~cmti ~output =
  let verify registry lemmas =
    let obligations = Vc_backend.lemma_obligations registry lemmas in
    let solver = Solver_backend.solver_identity () in
    List.map2
      (fun (lemma : Typed_core.axiom) (obligation : Refined_types.obligation) ->
        match Solver_backend.solve obligation with
        | Valid ->
            {
              artifact_version = 1;
              lemma_name = obligation.name;
              statement = Proof_artifact_io.canonical_statement lemma;
              statement_digest = Proof_artifact_io.statement_digest lemma;
              digest_algorithm = "sha256";
              vc_digest = Proof_artifact_io.sha256 obligation.smt;
              vc_smt = obligation.smt;
              solver;
              timeout_seconds = Solver_backend.timeout_seconds;
              trusted_axioms = obligation.trusted_axioms;
              checked_dependencies = obligation.checked_lemmas;
            }
        | Invalid model ->
            Refined_common.typed_error_at obligation.location
              "lemma `%s` is invalid:\n%s" obligation.name model
        | Unknown reason ->
            Refined_common.typed_error_at obligation.location
              "lemma `%s` could not be checked:\n%s" obligation.name reason)
      lemmas obligations
  in
  Ocaml_5_3_frontend.write_rmi ~verify ~cmti ~output

let replay_proof path =
  let bundle =
    try Proof_artifact_io.read path
    with Invalid_argument message ->
      Refined_common.typed_error_at Source_span.none
        "cannot parse proof artifact `%s`: %s" path message
  in
  (match Proof_artifact_io.validate bundle with
  | Ok () -> ()
  | Error message ->
      Refined_common.typed_error_at Source_span.none
        "proof artifact `%s` failed structural replay: %s" path message);
  List.iter
    (fun artifact ->
      let obligation =
        {
          name = artifact.lemma_name;
          mode = Over;
          location = Source_span.none;
          smt = artifact.vc_smt;
          trusted_axioms = artifact.trusted_axioms;
          checked_lemmas = artifact.checked_dependencies;
          proof_artifacts = [];
          ghost_instantiations = [];
        }
      in
      match Solver_backend.solve obligation with
      | Valid -> ()
      | Invalid model ->
          Refined_common.typed_error_at Source_span.none
            "proof replay failed for `%s`:\n%s" artifact.lemma_name model
      | Unknown reason ->
          Refined_common.typed_error_at Source_span.none
            "proof replay was inconclusive for `%s`:\n%s" artifact.lemma_name
            reason)
    bundle.artifacts;
  List.length bundle.artifacts

let solve = Solver_backend.solve
