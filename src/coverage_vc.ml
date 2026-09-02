open Refined_ir
open Refined_types
open Refined_common
open Vc_logic
open Heap_model
open Ownership
open Vc_encoding

let typed_outcome_coverage_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  let module R = Relational_outcome in
  let env = contract_argument_env function_def contract in
  let formula_env =
    List.map2
      (fun (symbol, sort) (_, value) ->
        (symbol.Typed_core.display, (value.term, sort)))
      function_def.arguments env
  in
  let parse text =
    parse_formula ~filename:contract.loc.file
      ~loc:(location_of_span contract.loc)
      text
  in
  let pre_expressions, post_expression = contract_expressions contract in
  let result_reference_sort = reference_content_sort function_def.result in
  let result_state_expression = Option.map parse contract.result_state in
  (match
     (result_reference_sort, result_state_expression, contract.result_fresh)
   with
  | Some _, None, _ ->
      typed_error_at contract.loc
        "a reference result requires result_state for escaping heap content"
  | None, Some _, _ ->
      typed_error_at contract.loc
        "result_state is valid only for a reference result"
  | None, None, true ->
      typed_error_at contract.loc
        "result_fresh is valid only for a reference result"
  | Some _, Some _, _ | None, None, false -> ());
  let program =
    typed_specialize_program program function_def pre_expressions
      post_expression
    |> fun program -> typed_monomorphize_datatypes program function_def
  in
  let owned_result_paths result =
    if result_reference_sort <> None then []
    else
      match
        returned_reference_paths ~recursive_frontier:contract.result_recursive
          program.registry ~result_sort:function_def.result ~result
      with
      | Ok paths -> paths
      | Error path ->
          typed_error_at contract.loc
            "recursive reachable-reference path `%s` needs an ownership \
             invariant"
            path
  in
  let owned_paths = owned_result_paths "missing_result" in
  let expected_owned_paths = List.map (fun path -> path.path) owned_paths in
  let actual_owned_paths = List.map fst contract.result_references in
  if result_reference_sort <> None then (
    if contract.result_references <> [] then
      typed_error_at contract.loc
        "direct reference results use result_state, not result_references";
    if contract.result_fresh_references <> [] then
      typed_error_at contract.loc
        "direct reference results use result_fresh, not result_fresh_references";
    if contract.result_reference_permissions <> [] || contract.result_recursive
    then
      typed_error_at contract.loc
        "direct reference results do not use nested ownership permissions")
  else if
    List.sort String.compare expected_owned_paths
    <> List.sort String.compare actual_owned_paths
    || List.length actual_owned_paths
       <> List.length (List.sort_uniq String.compare actual_owned_paths)
  then
    typed_error_at contract.loc
      "result_references must cover every finite returned reference path";
  if
    List.exists
      (fun path -> not (List.mem path expected_owned_paths))
      contract.result_fresh_references
  then
    typed_error_at contract.loc
      "result_fresh_references names an unknown returned reference path";
  validate_result_reference_permissions ~loc:contract.loc contract
    expected_owned_paths;
  let owned_result_expressions =
    List.map
      (fun path ->
        ( path,
          parse (List.assoc path.path contract.result_references),
          result_reference_is_transfer contract path.path ))
      owned_paths
  in
  let relation, choices, generic_calls =
    typed_relational_expr program analysis Under function_def
      ~initial_state:
        (typed_initial_reference_state ~registry:program.registry function_def)
      env function_def.body
  in
  if owned_paths <> [] then
    use_returned_reference_theory generic_calls program.registry
      function_def.result;
  if generic_calls.side_conditions <> [] then
    typed_error_at contract.loc
      "outcome coverage calls require constructive callee summaries";
  let required_region_expressions =
    contract.requires_regions
    |> List.concat_map (fun (name, region) ->
        let symbol, sort =
          List.find
            (fun ((symbol : Typed_core.symbol), _) -> symbol.display = name)
            function_def.arguments
        in
        let root = smt_identifier symbol.key in
        region_frontier_specs program contract.mode ~loc:contract.loc region
          ~root_sort:sort ~root
        |> List.map (fun (path, predicate, (owner : Source_span.t)) ->
            use_returned_reference_theory generic_calls program.registry sort;
            let predicate =
              parse_formula ~filename:owner.file ~loc:(location_of_span owner)
                predicate
            in
            (path, predicate)))
  in
  let formals =
    List.filter_map
      (fun ((symbol : Typed_core.symbol), sort) ->
        match reference_content_sort sort with
        | Some _ -> None
        | None -> Some (symbol.display, symbol.key, sort))
      function_def.arguments
  in
  let validate_witnesses witnesses =
    let expected = List.map (fun (name, _, _) -> name) formals in
    let actual = List.map fst witnesses in
    if witnesses = [] then []
    else (
      if
        List.sort String.compare expected <> List.sort String.compare actual
        || List.length actual
           <> List.length (List.sort_uniq String.compare actual)
      then
        typed_error_at contract.loc
          "outcome witnesses must define every parameter exactly once";
      List.map
        (fun (name, key, sort) ->
          (key, sort, parse (List.assoc name witnesses)))
        formals)
  in
  let normal_witnesses =
    if contract.witnesses = [] then None
    else Some (validate_witnesses contract.witnesses)
  in
  let normal_witness_relation = Option.map parse contract.witness_relation in
  let reference_cells = typed_reference_arguments function_def in
  let ghost_names = List.map fst contract.ghosts in
  let reserved_ghost_names =
    [ "result"; "payload"; "value"; "old" ]
    @ List.map (fun (name, _, _) -> name) formals
    @ List.map (fun (name, _, _) -> name) reference_cells
    @ List.map (fun (name, _, _) -> "old_" ^ name) reference_cells
    @ List.map fst contract.state
  in
  if
    List.length ghost_names
    <> List.length (List.sort_uniq String.compare ghost_names)
    || List.exists (fun name -> List.mem name reserved_ghost_names) ghost_names
  then
    typed_error_at contract.loc
      "ghost names must be unique and cannot shadow contract variables";
  let coverage_ghosts =
    List.mapi
      (fun index (name, sort) ->
        ( name,
          "coverage_ghost_" ^ string_of_int index ^ "_" ^ smt_identifier name,
          sort ))
      contract.ghosts
  in
  let ghost_env =
    List.map (fun (name, term, sort) -> (name, (term, sort))) coverage_ghosts
  in
  let old_reference_env =
    List.map
      (fun (name, key, sort) ->
        ("old_" ^ name, (app "select" [ initial_heap_name sort; key ], sort)))
      reference_cells
  in
  let state_cells = typed_local_cells function_def.body @ reference_cells in
  let state_targets =
    List.mapi
      (fun index (name, predicate) ->
        match List.find_opt (fun (cell, _, _) -> cell = name) state_cells with
        | Some (_, key, sort) ->
            ( name,
              key,
              sort,
              "missing_state_" ^ string_of_int index,
              parse predicate )
        | None ->
            typed_error_at contract.loc "coverage state names unknown cell `%s`"
              name)
      contract.state
  in
  let reference_names = List.map (fun (name, _, _) -> name) reference_cells in
  List.iter
    (fun name ->
      if not (List.mem name reference_names) then
        typed_error_at contract.loc
          "modifies footprint names non-reference parameter `%s`" name;
      if not (List.mem_assoc name contract.state) then
        typed_error_at contract.loc
          "coverage modifies `%s` needs a state target predicate" name)
    contract.modifies;
  let normal_modified_names =
    contract.modifies
    @ List.filter_map
        (fun (name, _) ->
          if List.mem name reference_names then Some name else None)
        contract.state
    |> List.sort_uniq String.compare
  in
  let outcome_modified_names kind outcome =
    List.filter_map
      (fun (candidate_kind, candidate, name) ->
        if candidate_kind = kind && candidate = outcome then Some name else None)
      contract.outcome_modifies
    @ List.filter_map
        (fun (candidate_kind, candidate, name, _predicate) ->
          if
            candidate_kind = kind && candidate = outcome
            && List.mem name reference_names
          then Some name
          else None)
        contract.outcome_state
    |> List.sort_uniq String.compare
  in
  let state_witnesses =
    let expected = List.map (fun (name, _, _) -> name) reference_cells in
    let actual = List.map fst contract.state_witnesses in
    if expected = [] && actual <> [] then
      typed_error_at contract.loc "state_witnesses name no reference parameters";
    if expected <> [] && actual <> [] then
      if
        List.sort String.compare expected <> List.sort String.compare actual
        || List.length actual
           <> List.length (List.sort_uniq String.compare actual)
      then
        typed_error_at contract.loc
          "state_witnesses must define every reference parameter exactly once";
    if actual = [] then []
    else
      List.map
        (fun (name, key, sort) ->
          (key, sort, parse (List.assoc name contract.state_witnesses)))
        reference_cells
  in
  let payload_sorts = typed_outcome_payload_sorts ~program function_def.body in
  let payload_sort kind name =
    let rec find = function
      | [] -> None
      | (candidate, candidate_name, sort) :: rest ->
          if candidate = kind && candidate_name = name then sort else find rest
    in
    find payload_sorts
  in
  let outcome_state_names =
    List.map
      (fun (kind, outcome, name, _) -> (kind, outcome, name))
      contract.outcome_state
  in
  List.iter
    (fun (kind, outcome, _name, _) ->
      if
        (kind <> "raise" && kind <> "perform")
        || not
             (List.exists
                (fun (candidate : Typed_core.coverage_outcome) ->
                  candidate.kind = kind && candidate.name = outcome)
                contract.outcomes)
      then
        typed_error_at contract.loc
          "outcome_state names undeclared coverage outcome `%s:%s`" kind outcome)
    contract.outcome_state;
  List.iter
    (fun (kind, outcome, name) ->
      if not (List.mem name reference_names) then
        typed_error_at contract.loc
          "outcome_modifies names non-reference parameter `%s`" name;
      if
        not
          (List.exists
             (fun (candidate : Typed_core.coverage_outcome) ->
               candidate.kind = kind && candidate.name = outcome)
             contract.outcomes)
      then
        typed_error_at contract.loc
          "outcome_modifies names undeclared coverage outcome `%s:%s`" kind
          outcome;
      if
        not
          (List.exists
             (fun (state_kind, state_outcome, state_name, _) ->
               state_kind = kind && state_outcome = outcome && state_name = name)
             contract.outcome_state)
      then
        typed_error_at contract.loc
          "coverage outcome modifies `%s` needs a state target predicate" name)
    contract.outcome_modifies;
  if
    List.length outcome_state_names
    <> List.length (List.sort_uniq compare outcome_state_names)
  then
    typed_error_at contract.loc
      "outcome_state clauses must name each outcome cell once";
  let outcomes =
    List.mapi
      (fun outcome_index (outcome : Typed_core.coverage_outcome) ->
        let kind =
          match outcome.kind with
          | "raise" -> `Raised
          | "perform" -> `Performed
          | kind ->
              typed_error_at contract.loc "unknown coverage outcome kind `%s`"
                kind
        in
        let sort = payload_sort kind outcome.name in
        let outcome_state =
          contract.outcome_state
          |> List.filter (fun (candidate_kind, candidate, _, _) ->
              candidate_kind = outcome.kind && candidate = outcome.name)
          |> List.mapi (fun state_index (_, _, name, predicate) ->
              match
                List.find_opt (fun (cell, _, _) -> cell = name) state_cells
              with
              | Some (_, key, sort) ->
                  ( name,
                    key,
                    sort,
                    Printf.sprintf "missing_outcome_state_%d_%d" outcome_index
                      state_index,
                    parse predicate )
              | None ->
                  typed_error_at contract.loc
                    "outcome_state names unknown cell `%s`" name)
        in
        ( kind,
          outcome.name,
          sort,
          parse outcome.post,
          validate_witnesses outcome.witnesses,
          Option.map parse outcome.witness_relation,
          outcome_state ))
      contract.outcomes
  in
  let state_target_env =
    List.map
      (fun (name, _, sort, target, _) -> (name, (target, sort)))
      state_targets
  in
  let result_state_target =
    Option.map
      (fun expression ->
        (Option.get result_reference_sort, "missing_result_state", expression))
      result_state_expression
  in
  let owned_result_targets =
    List.mapi
      (fun index (path, expression, fresh) ->
        ( path,
          "missing_result_reference_" ^ string_of_int index,
          expression,
          fresh ))
      owned_result_expressions
  in
  let owned_result_env =
    List.concat_map
      (fun (path, target, _expression, _fresh) ->
        [
          (returned_reference_value_name path.path, (target, path.content_sort));
          ( returned_reference_identity_name path.path,
            (path.identity, reference_sort path.content_sort) );
        ])
      owned_result_targets
  in
  let result_target_env =
    ("result", ("missing_result", function_def.result))
    :: Option.fold ~none:[]
         ~some:(fun (sort, target, _) -> [ ("result_value", (target, sort)) ])
         result_state_target
    @ owned_result_env @ state_target_env
  in
  let roots =
    generic_calls.used_theory_symbols
    @ List.concat_map
        (formula_theory_symbols program.registry formula_env)
        pre_expressions
    @ List.concat_map
        (fun (path, expression) ->
          formula_theory_symbols program.registry
            [
              ("identity", (path.identity, reference_sort path.content_sort));
              ("value", ("region_value", path.content_sort));
            ]
            expression)
        required_region_expressions
    @ formula_theory_symbols program.registry
        (match (normal_witness_relation, normal_witnesses) with
        | Some _, _ | None, Some _ -> result_target_env
        | None, None -> result_target_env @ formula_env)
        post_expression
    @ Option.fold ~none:[]
        ~some:(fun (sort, target, expression) ->
          formula_theory_symbols program.registry
            (("value", (target, sort)) :: result_target_env)
            expression)
        result_state_target
    @ List.concat_map
        (fun (path, target, expression, _fresh) ->
          formula_theory_symbols program.registry
            (("identity", (path.identity, reference_sort path.content_sort))
            :: ("value", (target, path.content_sort))
            :: result_target_env)
            expression)
        owned_result_targets
    @ Option.fold ~none:[]
        ~some:(fun witnesses ->
          List.concat_map
            (fun (_, sort, expression) ->
              formula_theory_symbols ~expected:sort program.registry
                (ghost_env @ result_target_env)
                expression)
            witnesses)
        normal_witnesses
    @ Option.fold ~none:[]
        ~some:(fun relation ->
          formula_theory_symbols program.registry
            (ghost_env @ result_target_env @ formula_env @ old_reference_env)
            relation)
        normal_witness_relation
    @ List.concat_map
        (fun (_, _, sort, post, witnesses, relation, outcome_state) ->
          let payload_env =
            match sort with
            | Some sort -> [ ("payload", ("missing_payload", sort)) ]
            | None -> []
          in
          let target_env =
            List.map
              (fun (name, _, sort, target, _) -> (name, (target, sort)))
              outcome_state
            @ payload_env
          in
          let witness_env = ghost_env @ target_env in
          formula_theory_symbols program.registry target_env post
          @ List.concat_map
              (fun (_, formal_sort, expression) ->
                formula_theory_symbols ~expected:formal_sort program.registry
                  witness_env expression)
              witnesses
          @ List.concat_map
              (fun (_name, _key, state_sort, target, predicate) ->
                formula_theory_symbols program.registry
                  (("value", (target, state_sort)) :: target_env)
                  predicate)
              outcome_state
          @ Option.fold ~none:[]
              ~some:(fun relation ->
                formula_theory_symbols program.registry
                  (witness_env @ formula_env @ old_reference_env)
                  relation)
              relation
          @ List.concat_map
              (fun (_, witness_sort, expression) ->
                formula_theory_symbols ~expected:witness_sort program.registry
                  witness_env expression)
              state_witnesses)
        outcomes
    @ List.concat_map
        (fun (_name, _key, sort, target, predicate) ->
          formula_theory_symbols program.registry
            (("value", (target, sort)) :: result_target_env)
            predicate)
        state_targets
    @ List.concat_map
        (fun (_, sort, expression) ->
          formula_theory_symbols ~expected:sort program.registry
            (ghost_env @ result_target_env)
            expression)
        state_witnesses
    @ List.concat_map
        (fun (name, predicate) ->
          match
            List.find_opt (fun (cell, _, _) -> cell = name) reference_cells
          with
          | Some (_, _, sort) ->
              formula_theory_symbols program.registry
                [ ("value", ("initial_state_value", sort)) ]
                (parse predicate)
          | None ->
              typed_error_at contract.loc
                "requires_state names non-reference parameter `%s`" name)
        contract.requires_state
    |> List.sort_uniq String.compare
  in
  let program, _ = slice_program_theory program ~roots in
  let required_state_posts =
    List.map
      (fun (name, predicate) ->
        let _, key, sort =
          List.find (fun (cell, _, _) -> cell = name) reference_cells
        in
        let predicate =
          typed_formula program.registry
            [ ("value", ("initial_state_value", sort)) ]
            (parse predicate)
        in
        Printf.sprintf "(let ((initial_state_value %s)) %s)"
          (app "select" [ initial_heap_name sort; key ])
          predicate)
      contract.requires_state
  in
  let required_region_posts =
    List.map
      (fun (path, expression) ->
        let content =
          app "select" [ initial_heap_name path.content_sort; path.identity ]
        in
        let predicate =
          typed_formula program.registry
            [
              ("identity", (path.identity, reference_sort path.content_sort));
              ("value", ("region_value", path.content_sort));
            ]
            expression
        in
        app "=>"
          [
            path.guard;
            Printf.sprintf "(let ((region_value %s)) %s)" content predicate;
          ])
      required_region_expressions
  in
  let pre =
    and_
      (List.map (typed_formula program.registry formula_env) pre_expressions
      @ required_state_posts @ required_region_posts)
  in
  let heap_declarations =
    typed_initial_reference_state ~registry:program.registry function_def
    |> List.map (fun (key, _) ->
        let sort =
          typed_function_reference_sorts ~registry:program.registry function_def
          |> List.find_opt (fun sort -> heap_key sort = key)
          |> Option.get
        in
        ( initial_heap_name sort,
          Printf.sprintf "(Array %s %s)"
            (typed_smt_sort (reference_sort sort))
            (typed_smt_sort sort) ))
  in
  let reference_declarations =
    List.map
      (fun (_name, identity, sort) ->
        (identity, typed_smt_sort (reference_sort sort)))
      reference_cells
  in
  let choices_declarations =
    List.map (fun (name, sort) -> (name, typed_smt_sort sort)) choices
  in
  let exists_choices formula =
    Refinement_domain.Smt.exists choices_declarations formula
  in
  let ghost_declarations =
    List.map
      (fun (_name, term, sort) -> (term, typed_smt_sort sort))
      coverage_ghosts
  in
  let exists_ghosts formula =
    Refinement_domain.Smt.exists ghost_declarations formula
  in
  let ordinary_input_declarations =
    List.map (fun (_, key, sort) -> (key, typed_smt_sort sort)) formals
  in
  let reference_input_declarations =
    reference_declarations @ heap_declarations
  in
  let input_declarations =
    ordinary_input_declarations @ reference_input_declarations
  in
  let exists_inputs formula =
    Refinement_domain.Smt.exists input_declarations formula
  in
  let forall_inputs_and_ghosts formula =
    Refinement_domain.Smt.forall
      (ghost_declarations @ input_declarations)
      formula
  in
  let let_arguments target_env witnesses formula =
    let bindings =
      List.map
        (fun (key, sort, expression) ->
          ( key,
            typed_formula ~expected:sort program.registry target_env expression
          ))
        witnesses
    in
    "(let ("
    ^ String.concat " "
        (List.map
           (fun (name, term) -> Printf.sprintf "(%s %s)" name term)
           bindings)
    ^ ") " ^ formula ^ ")"
  in
  let initial_state_guards target_env =
    List.map
      (fun (identity, sort, expression) ->
        app "="
          [
            app "select" [ initial_heap_name sort; identity ];
            typed_formula ~expected:sort program.registry target_env expression;
          ])
      state_witnesses
  in
  let with_relational_assumptions target_env formula =
    and_
      (((formula :: List.rev generic_calls.summary_assumptions)
       @ List.rev generic_calls.semantic_assumptions)
      @ initial_state_guards target_env)
  in
  let normal_paths =
    relation
    |> List.filter_map (fun path ->
        match path.R.outcome with
        | Return value ->
            let state_equalities =
              List.map
                (fun (_name, key, sort, target, _) ->
                  app "=" [ heap_select path.final_state key sort; target ])
                state_targets
            in
            let result_equalities =
              Option.fold ~none:[]
                ~some:(fun (sort, target, _) ->
                  [
                    app "=" [ heap_select path.final_state value sort; target ];
                  ])
                result_state_target
            in
            let owned_result_equalities =
              let actual_paths = owned_result_paths value in
              let equalities =
                List.concat_map
                  (fun (target_path, target, _expression, fresh) ->
                    let owned_path =
                      List.find
                        (fun path -> path.path = target_path.path)
                        actual_paths
                    in
                    let content =
                      heap_select path.final_state owned_path.identity
                        owned_path.content_sort
                    in
                    let equality =
                      app "=>" [ owned_path.guard; app "=" [ content; target ] ]
                    in
                    if not fresh then
                      let identities =
                        reference_cells
                        |> List.filter_map (fun (_name, identity, sort) ->
                            if
                              typed_smt_sort sort
                              = typed_smt_sort owned_path.content_sort
                            then Some identity
                            else None)
                      in
                      [
                        app "=>"
                          [
                            owned_path.guard;
                            or_
                              (List.map
                                 (fun identity ->
                                   app "=" [ owned_path.identity; identity ])
                                 identities);
                          ];
                        equality;
                      ]
                    else
                      let identities =
                        List.map
                          (fun (_, identity, _) -> identity)
                          reference_cells
                      in
                      match identities with
                      | [] -> [ equality ]
                      | identities ->
                          [
                            app "=>"
                              [
                                owned_path.guard;
                                app "distinct"
                                  (owned_path.identity :: identities);
                              ];
                            equality;
                          ])
                  owned_result_targets
              in
              let distinctness =
                owned_result_targets
                |> List.filter_map
                     (fun (target_path, _target, _expression, fresh) ->
                       if not fresh then None
                       else
                         let path =
                           List.find
                             (fun path -> path.path = target_path.path)
                             actual_paths
                         in
                         Some (path.identity, path.content_sort, path.guard))
                |> guarded_identity_distinctness
              in
              equalities @ distinctness
            in
            let freshness =
              if not contract.result_fresh then []
              else
                let identities =
                  List.map (fun (_, identity, _) -> identity) reference_cells
                in
                match identities with
                | [] -> []
                | identities -> [ app "distinct" (value :: identities) ]
            in
            Some
              (and_
                 (path.guard
                  :: app "=" [ value; "missing_result" ]
                  :: state_equalities
                 @ result_equalities @ owned_result_equalities @ freshness
                 @ frame_obligations ~initial:path.initial_state
                     ~final:path.final_state ~references:reference_cells
                     ~modified:
                       (reference_modified_identities reference_cells
                          normal_modified_names)))
        | Raised _ | Performed _ -> None)
    |> or_
  in
  let normal_witness_env = ghost_env @ result_target_env in
  let normal_post_env =
    match (normal_witness_relation, normal_witnesses) with
    | Some _, _ | None, Some _ -> result_target_env
    | None, None -> result_target_env @ formula_env
  in
  let obligations =
    let state_posts =
      List.map
        (fun (_name, _key, sort, target, predicate) ->
          typed_formula program.registry
            (("value", (target, sort)) :: result_target_env)
            predicate)
        state_targets
    in
    let result_posts =
      Option.fold ~none:[]
        ~some:(fun (sort, target, expression) ->
          [
            typed_formula program.registry
              (("value", (target, sort)) :: result_target_env)
              expression;
          ])
        result_state_target
    in
    let owned_result_posts =
      List.map
        (fun (path, target, expression, _fresh) ->
          let predicate =
            typed_formula program.registry
              (("identity", (path.identity, reference_sort path.content_sort))
              :: ("value", (target, path.content_sort))
              :: result_target_env)
              expression
          in
          app "=>" [ path.guard; predicate ])
        owned_result_targets
    in
    let target =
      and_
        (typed_formula program.registry normal_post_env post_expression
         :: state_posts
        @ result_posts @ owned_result_posts)
    in
    match normal_witness_relation with
    | Some relation ->
        let relation =
          typed_formula program.registry
            (normal_witness_env @ formula_env @ old_reference_env)
            relation
        in
        let witness_assumptions =
          and_ (relation :: initial_state_guards normal_witness_env)
        in
        let totality =
          app "=>" [ target; exists_ghosts (exists_inputs witness_assumptions) ]
        in
        let execution =
          and_
            ((pre :: normal_paths :: List.rev generic_calls.summary_assumptions)
            @ List.rev generic_calls.semantic_assumptions)
          |> exists_choices
        in
        let soundness =
          app "=>" [ and_ [ target; witness_assumptions ]; execution ]
          |> forall_inputs_and_ghosts
        in
        [ totality; soundness ]
    | None ->
        let reachable =
          and_ [ pre; normal_paths ]
          |> with_relational_assumptions normal_witness_env
          |> exists_choices
        in
        let reachable =
          match normal_witnesses with
          | Some witnesses ->
              Refinement_domain.Smt.exists reference_input_declarations
                (let_arguments normal_witness_env witnesses reachable)
          | None -> exists_inputs reachable
        in
        [ app "=>" [ target; exists_ghosts reachable ] ]
  in
  let payload_declarations = ref [] in
  let outcome_obligations =
    List.mapi
      (fun index
           (kind, name, sort, post, witnesses, witness_relation, outcome_state)
         ->
        let target = "missing_payload_" ^ string_of_int index in
        let payload_env =
          match sort with
          | Some sort ->
              payload_declarations := (target, sort) :: !payload_declarations;
              [ ("payload", (target, sort)) ]
          | None -> []
        in
        let target_env =
          List.map
            (fun (name, _, sort, target, _) -> (name, (target, sort)))
            outcome_state
          @ payload_env
        in
        let witness_env = ghost_env @ target_env in
        let matching =
          relation
          |> List.filter_map (fun (path : R.path) ->
              let kind_name =
                match kind with `Raised -> "raise" | `Performed -> "perform"
              in
              let frames =
                frame_obligations ~initial:path.initial_state
                  ~final:path.final_state ~references:reference_cells
                  ~modified:
                    (reference_modified_identities reference_cells
                       (outcome_modified_names kind_name name))
              in
              let state_equalities =
                List.map
                  (fun (_name, key, state_sort, state_target, _) ->
                    app "="
                      [
                        heap_select path.final_state key state_sort;
                        state_target;
                      ])
                  outcome_state
              in
              match (kind, path.R.outcome) with
              | `Raised, Raised raised when raised.exception_ = name -> (
                  match (sort, raised.payload) with
                  | Some _, Some payload ->
                      Some
                        (and_
                           (path.guard
                            :: app "=" [ payload; target ]
                            :: state_equalities
                           @ frames))
                  | None, None ->
                      Some (and_ ((path.guard :: state_equalities) @ frames))
                  | _ -> None)
              | `Performed, Performed performed when performed.operation = name
                -> (
                  match (sort, performed.payload) with
                  | Some _, Some payload ->
                      Some
                        (and_
                           (path.guard
                            :: app "=" [ payload; target ]
                            :: state_equalities
                           @ frames))
                  | None, None ->
                      Some (and_ ((path.guard :: state_equalities) @ frames))
                  | _ -> None)
              | _ -> None)
          |> or_
        in
        let state_posts =
          List.map
            (fun (_name, _key, state_sort, state_target, predicate) ->
              typed_formula program.registry
                (("value", (state_target, state_sort)) :: target_env)
                predicate)
            outcome_state
        in
        let target_condition =
          and_ (typed_formula program.registry target_env post :: state_posts)
        in
        match witness_relation with
        | Some relation ->
            let relation =
              typed_formula program.registry
                (witness_env @ formula_env @ old_reference_env)
                relation
            in
            let witness_assumptions =
              and_ (relation :: initial_state_guards witness_env)
            in
            let totality =
              app "=>"
                [
                  target_condition;
                  exists_ghosts (exists_inputs witness_assumptions);
                ]
            in
            let execution =
              and_
                ((pre :: matching :: List.rev generic_calls.summary_assumptions)
                @ List.rev generic_calls.semantic_assumptions)
              |> exists_choices
            in
            let soundness =
              app "=>"
                [ and_ [ target_condition; witness_assumptions ]; execution ]
              |> forall_inputs_and_ghosts
            in
            and_ [ totality; soundness ]
        | None ->
            let reachable =
              and_ [ pre; matching ]
              |> with_relational_assumptions witness_env
              |> exists_choices
            in
            let reachable =
              if witnesses = [] then exists_inputs reachable
              else
                Refinement_domain.Smt.exists reference_input_declarations
                  (let_arguments witness_env witnesses reachable)
            in
            app "=>" [ target_condition; exists_ghosts reachable ])
      outcomes
  in
  let obligation = and_ (obligations @ outcome_obligations) in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer (typed_datatype_prelude program function_def);
  Buffer.add_string buffer
    (Printf.sprintf "(declare-const missing_result %s)\n"
       (typed_smt_sort function_def.result));
  Option.iter
    (fun (sort, target, _) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" target (typed_smt_sort sort)))
    result_state_target;
  List.iter
    (fun (path, target, _expression, _fresh) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" target
           (typed_smt_sort path.content_sort)))
    owned_result_targets;
  let identity_capacity_sorts =
    List.map (fun (_name, _identity, sort) -> sort) reference_cells
    @ List.filter_map (fun (_name, sort) -> reference_content_sort sort) choices
  in
  identity_capacity_sorts
  |> List.sort_uniq (fun left right ->
      String.compare (typed_smt_sort left) (typed_smt_sort right))
  |> List.iter (fun sort ->
      let count =
        List.fold_left
          (fun count candidate ->
            if typed_smt_sort candidate = typed_smt_sort sort then count + 1
            else count)
          0 identity_capacity_sorts
      in
      let witnesses =
        List.init count (fun index ->
            Printf.sprintf "heap_identity_witness_%s_%d"
              (smt_identifier (typed_smt_sort sort))
              index)
      in
      List.iter
        (fun witness ->
          Buffer.add_string buffer
            (Printf.sprintf "(declare-const %s %s)\n" witness
               (typed_smt_sort (reference_sort sort))))
        witnesses;
      if List.length witnesses > 1 then
        Buffer.add_string buffer
          (Printf.sprintf "(assert %s)\n" (app "distinct" witnesses)));
  List.iter
    (fun (_name, _key, sort, target, _) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" target (typed_smt_sort sort)))
    state_targets;
  List.iter
    (fun (_, _, _, _, _, _, outcome_state) ->
      List.iter
        (fun (_name, _key, sort, target, _) ->
          Buffer.add_string buffer
            (Printf.sprintf "(declare-const %s %s)\n" target
               (typed_smt_sort sort)))
        outcome_state)
    outcomes;
  List.iter
    (fun (name, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" name (typed_smt_sort sort)))
    (List.rev !payload_declarations);
  Buffer.add_string buffer (Printf.sprintf "(assert (not %s))\n" obligation);
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
