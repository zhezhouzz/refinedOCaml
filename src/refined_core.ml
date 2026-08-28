open Refined_ir
include Refined_types

let obligations_of_cmt = Vc_backend.obligations_of_cmt

let obligations_of_cmt_with_theories =
  Vc_backend.obligations_of_cmt_with_theories

let write_rmi ~cmti ~output =
  let verify registry lemmas =
    let obligations = Vc_backend.lemma_obligations registry lemmas in
    let solver = Solver_backend.solver_identity () in
    List.map
      (fun (obligation : Refined_types.obligation) ->
        match Solver_backend.solve obligation with
        | Valid ->
            {
              lemma_name = obligation.name;
              vc_digest = Digest.to_hex (Digest.string obligation.smt);
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
      obligations
  in
  Ocaml_5_3_frontend.write_rmi ~verify ~cmti ~output

let solve = Solver_backend.solve
