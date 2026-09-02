open Refined_ir
open Refined_types
open Refined_common
open Vc_logic
open Ownership
open Vc_encoding

let lemma_obligations registry lemmas =
  let registry =
    {
      registry with
      Typed_core.lemmas = [];
      checked_lemmas = [];
      proof_artifacts = [];
    }
  in
  let obligation (lemma : Typed_core.axiom) =
    let arguments =
      List.map
        (fun (name, sort) ->
          ( Typed_core.
              { key = "lemma." ^ lemma.axiom_name ^ "." ^ name; display = name },
            sort ))
        (List.map (fun (_, name, sort) -> (name, sort)) lemma.binders)
    in
    let dummy =
      Typed_core.
        {
          symbol =
            { key = "lemma." ^ lemma.axiom_name; display = lemma.axiom_name };
          arguments;
          result = S_unit;
          body =
            {
              desc = Bool true;
              sort = S_bool;
              refinement = None;
              loc = lemma.loc;
            };
          contracts = [];
          measure = [];
        }
    in
    let formula =
      parse_formula ~filename:lemma.loc.file
        ~loc:(location_of_span lemma.loc)
        lemma.body
    in
    let env =
      List.map
        (fun (name, sort) -> (name, (smt_identifier name, sort)))
        (List.map (fun (_, name, sort) -> (name, sort)) lemma.binders)
    in
    let roots =
      formula_theory_symbols ~scope:lemma.scope registry env formula
    in
    let program = Typed_core.{ registry; functions = [] } in
    let program, _enabled_symbols = slice_program_theory program ~roots in
    let sliced_registry = program.Typed_core.registry in
    let body = typed_formula ~scope:lemma.scope sliced_registry env formula in
    let theorem =
      List.fold_right
        (fun (quantifier, name, sort) body ->
          let quantifier =
            match quantifier with
            | Typed_core.Forall -> "forall"
            | Exists -> "exists"
          in
          let binder =
            Printf.sprintf "((%s %s))" (smt_identifier name)
              (typed_smt_sort sort)
          in
          app quantifier [ binder; body ])
        lemma.binders body
    in
    let buffer = Buffer.create 4096 in
    Buffer.add_string buffer
      "(set-option :produce-models true)\n(set-logic ALL)\n";
    Buffer.add_string buffer (typed_datatype_prelude program dummy);
    Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" theorem);
    Buffer.add_string buffer "(check-sat)\n(get-model)\n";
    {
      name = lemma.axiom_name;
      mode = Over;
      location = lemma.loc;
      smt = Buffer.contents buffer;
      trusted_axioms =
        List.rev_map
          (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
          sliced_registry.axioms;
      checked_lemmas =
        List.rev_map
          (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
          sliced_registry.checked_lemmas;
      proof_artifacts = List.rev sliced_registry.proof_artifacts;
      ghost_instantiations = [];
    }
  in
  List.map
    (fun lemma ->
      let result = obligation lemma in
      registry.checked_lemmas <- lemma :: registry.checked_lemmas;
      result)
    lemmas

let obligations_of_cmt_with_theories ~theories filename =
  let program = Ocaml_5_5_frontend.program_of_cmt ~theories filename in
  let analysis = Function_analysis.analyze program in
  List.concat_map
    (fun function_def ->
      List.map
        (fun contract ->
          validate_region_contracts program function_def contract;
          if
            typed_requires_relational program function_def.Typed_core.body
            || contract.Typed_core.mode = Under
               && (contract.witness_relation <> None || contract.ghosts <> [])
            || sort_reaches_reference program.registry function_def.result
            || contract.result_state <> None
            || contract.result_fresh
            || contract.result_references <> []
            || contract.result_fresh_references <> []
          then
            if contract.Typed_core.mode = Under then
              Coverage_vc.typed_outcome_coverage_obligation program analysis
                function_def contract
            else
              Outcome_vc.typed_exception_obligation program analysis
                function_def contract
          else Pure_vc.typed_obligation program analysis function_def contract)
        function_def.Typed_core.contracts)
    program.functions

let obligations_of_cmt filename =
  obligations_of_cmt_with_theories ~theories:[] filename
