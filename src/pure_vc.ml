open Refined_ir
open Refined_types
open Refined_common
open Vc_logic
open Vc_encoding

let typed_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let original_arity = List.length function_def.arguments in
  let function_def, contract, coverage_observation_arity =
    eta_expand_function_result function_def contract
  in
  let is_universal index ((symbol : Typed_core.symbol), _) =
    contract.mode = Under
    && (index >= original_arity || List.mem symbol.display contract.universals)
  in
  let env = contract_argument_env function_def contract in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let universal_formula_env =
    List.filteri
      (fun index _ ->
        is_universal index (List.nth function_def.arguments index))
      formula_env
  in
  let pre_expressions, post_expression = contract_expressions contract in
  let existential_pre_expressions, universal_pre_expressions =
    contract_domain_expressions contract
    |> List.partition (fun (index, _) ->
        not (is_universal index (List.nth function_def.arguments index)))
    |> fun (existential, universal) ->
    (List.map snd existential, List.map snd universal)
  in
  let witness_expressions =
    match contract.witnesses with
    | [] -> []
    | witnesses ->
        if contract.mode <> Under then assert false;
        let names = List.map fst witnesses in
        let existential_parameters =
          List.filteri
            (fun index argument ->
              index < original_arity && not (is_universal index argument))
            function_def.arguments
        in
        let expected =
          List.map
            (fun ((symbol : Typed_core.symbol), _) -> symbol.display)
            existential_parameters
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
          existential_parameters
  in
  let program =
    typed_specialize_program program function_def pre_expressions
      post_expression
  in
  let program = typed_monomorphize_datatypes program function_def in
  let body, choices, generic_calls =
    typed_expr_smt program analysis contract.mode function_def env
      function_def.body
  in
  let roots =
    generic_calls.used_theory_symbols
    @ List.concat_map
        (formula_theory_symbols program.registry formula_env)
        pre_expressions
    @ formula_theory_symbols program.registry
        (("result", ("result", function_def.result)) :: formula_env)
        post_expression
    @ List.concat_map
        (fun (_, sort, expression) ->
          formula_theory_symbols ~expected:sort program.registry
            (("result", ("missing_result", function_def.result))
            :: universal_formula_env)
            expression)
        witness_expressions
    |> List.sort_uniq String.compare
  in
  let program, _enabled_symbols = slice_program_theory program ~roots in
  let typed_pre expressions =
    and_ (List.map (typed_formula program.registry formula_env) expressions)
  in
  let existential_pre = typed_pre existential_pre_expressions in
  let universal_pre = typed_pre universal_pre_expressions in
  let pre = and_ [ existential_pre; universal_pre ] in
  let result_name =
    match contract.mode with Over -> "result" | Under -> "missing_result"
  in
  let post_env =
    let result = ("result", (result_name, function_def.result)) in
    match contract.mode with
    | Over -> result :: formula_env
    | Under -> result :: universal_formula_env
  in
  let post = typed_formula program.registry post_env post_expression in
  let argument_witnesses =
    List.map
      (fun (symbol, sort, expression) ->
        ( smt_identifier symbol.Typed_core.key,
          typed_formula ~expected:sort program.registry
            (("result", (result_name, function_def.result))
            :: universal_formula_env)
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
  let arguments =
    List.map
      (fun (symbol, sort) ->
        (smt_identifier symbol.Typed_core.key, typed_smt_sort sort))
      function_def.arguments
  in
  let witness_arguments, universal_arguments =
    List.mapi
      (fun index argument ->
        (is_universal index (List.nth function_def.arguments index), argument))
      arguments
    |> List.partition (fun (universal, _) -> not universal)
    |> fun (existential, universal) ->
    (List.map snd existential, List.map snd universal)
  in
  if
    contract.mode = Under
    && List.length
         (List.filteri (fun index _ -> index >= original_arity) arguments)
       <> coverage_observation_arity
  then invalid_arg "coverage function-result observation arity mismatch";
  let choices =
    List.map (fun (name, sort) -> (name, typed_smt_sort sort)) choices
  in
  let assumptions = List.rev generic_calls.summary_assumptions in
  let side_conditions = List.rev generic_calls.side_conditions in
  let declare (name, sort) =
    Buffer.add_string buffer
      (Printf.sprintf "(declare-const %s %s)\n" name sort)
  in
  let add_side_conditions obligation =
    match side_conditions with
    | [] -> obligation
    | _ -> and_ [ app "=>" [ pre; and_ side_conditions ]; obligation ]
  in
  (match contract.mode with
  | Over ->
      List.iter declare arguments;
      List.iter declare choices;
      let actual = app "=" [ "result"; body.term ] in
      let obligation =
        app "=>" [ and_ ((pre :: assumptions) @ [ actual ]); post ]
        |> add_side_conditions
      in
      Buffer.add_string buffer
        (Printf.sprintf "(assert (not (let ((result %s)) %s)))\n" body.term
           obligation)
  | Under ->
      List.iter declare universal_arguments;
      let missing = "missing_result" in
      let body_formula =
        and_ (pre :: app "=" [ missing; body.term ] :: assumptions)
      in
      let actual =
        match argument_witnesses with
        | [] -> smt_exists (witness_arguments @ choices) body_formula
        | bindings ->
            let bindings =
              "("
              ^ String.concat " "
                  (List.map
                     (fun (name, term) -> Printf.sprintf "(%s %s)" name term)
                     bindings)
              ^ ")"
            in
            smt_exists choices
              (Printf.sprintf "(let %s %s)" bindings body_formula)
      in
      let obligation =
        app "=>" [ and_ [ universal_pre; post ]; actual ] |> add_side_conditions
      in
      if side_conditions <> [] then (
        List.iter declare witness_arguments;
        List.iter declare choices);
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" missing
           (typed_smt_sort function_def.result));
      Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" obligation));
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
