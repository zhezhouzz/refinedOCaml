open Refined_ir
open Refined_types
open Refined_common
open Vc_logic
open Vc_encoding

let typed_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let env =
    List.map
      (fun (symbol, _) ->
        ( symbol.Typed_core.key,
          { term = smt_identifier symbol.key; refinement = None } ))
      function_def.Typed_core.arguments
  in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let pre_expression =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      contract.pre
  in
  let post_expression =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      contract.post
  in
  let witness_expressions =
    match contract.witnesses with
    | [] -> []
    | witnesses ->
        if contract.mode <> Under then assert false;
        let names = List.map fst witnesses in
        let expected =
          List.map
            (fun ((symbol : Typed_core.symbol), _) -> symbol.display)
            function_def.arguments
        in
        if
          List.sort String.compare names <> List.sort String.compare expected
          || List.length names
             <> List.length (List.sort_uniq String.compare names)
        then
          typed_error_at contract.loc
            "coverage witnesses must define every parameter exactly once";
        List.map
          (fun ((symbol : Typed_core.symbol), sort) ->
            let text = List.assoc symbol.display witnesses in
            let expression =
              parse_formula ~filename:contract.loc.file
                ~loc:(location_of_span contract.loc)
                text
            in
            (symbol, sort, expression))
          function_def.arguments
  in
  let program =
    typed_specialize_program program function_def pre_expression post_expression
  in
  let program = typed_monomorphize_datatypes program function_def in
  let body, choices, generic_calls =
    typed_expr_smt program analysis contract.mode function_def env
      function_def.body
  in
  let roots =
    generic_calls.used_theory_symbols
    @ formula_theory_symbols program.registry formula_env pre_expression
    @ formula_theory_symbols program.registry
        (("result", ("result", function_def.result)) :: formula_env)
        post_expression
    @ List.concat_map
        (fun (_, sort, expression) ->
          formula_theory_symbols ~expected:sort program.registry
            [ ("result", ("missing_result", function_def.result)) ]
            expression)
        witness_expressions
    |> List.sort_uniq String.compare
  in
  let program, _enabled_symbols = slice_program_theory program ~roots in
  let pre = typed_formula program.registry formula_env pre_expression in
  let result_name =
    match contract.mode with Over -> "result" | Under -> "missing_result"
  in
  let post_env =
    let result = ("result", (result_name, function_def.result)) in
    if witness_expressions = [] then result :: formula_env else [ result ]
  in
  let post = typed_formula program.registry post_env post_expression in
  let argument_witnesses =
    List.map
      (fun (symbol, sort, expression) ->
        ( smt_identifier symbol.Typed_core.key,
          typed_formula ~expected:sort program.registry
            [ ("result", (result_name, function_def.result)) ]
            expression ))
      witness_expressions
  in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  Hashtbl.iter
    (fun name (arguments, result) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-fun %s (%s) %s)\n" name
           (String.concat " " arguments)
           result))
    generic_calls.runtime_declarations;
  Vc_semantics.encode contract.mode
    {
      buffer;
      arguments =
        List.map
          (fun (symbol, sort) ->
            (smt_identifier symbol.Typed_core.key, typed_smt_sort sort))
          function_def.arguments;
      choices =
        List.map (fun (name, sort) -> (name, typed_smt_sort sort)) choices;
      result_sort = typed_smt_sort function_def.result;
      body = body.term;
      pre;
      post;
      assumptions = List.rev generic_calls.summary_assumptions;
      side_conditions = List.rev generic_calls.side_conditions;
      argument_witnesses;
    };
  Buffer.add_string buffer "(check-sat)\n(get-model)\n";
  {
    name = function_def.symbol.display;
    mode = contract.mode;
    location = contract.loc;
    smt = Buffer.contents buffer;
    trusted_axioms =
      List.rev_map
        (fun (axiom : Typed_core.axiom) -> axiom.axiom_name)
        program.registry.axioms;
    checked_lemmas =
      List.rev_map
        (fun (lemma : Typed_core.axiom) -> lemma.axiom_name)
        program.registry.checked_lemmas;
    proof_artifacts = List.rev program.registry.proof_artifacts;
    ghost_instantiations = List.rev generic_calls.ghost_instantiations;
  }
