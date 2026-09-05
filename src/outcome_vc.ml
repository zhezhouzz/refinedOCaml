open Refined_ir
open Refined_types
open Refined_common
open Vc_logic
open Heap_model
open Ownership
open Vc_encoding

let typed_exception_obligation (program : Typed_core.program) analysis
    (function_def : Typed_core.function_def) (contract : Typed_core.contract) =
  if contract.mode <> Over then
    typed_error_at contract.loc
      "exceptionful coverage contracts are not yet supported";
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
  let outcome_payloads =
    typed_outcome_payload_sorts ~program function_def.body
  in
  let payload_sort kind name =
    let rec find = function
      | [] -> None
      | (candidate, candidate_name, sort) :: rest ->
          if candidate = kind && candidate_name = name then sort else find rest
    in
    find outcome_payloads
  in
  let raised_expressions =
    contract.raises
    |> List.map (fun (name, predicate) ->
        (name, payload_sort `Raised name, parse predicate))
  in
  let performed_expressions =
    contract.performs
    |> List.map (fun (name, predicate) ->
        (name, payload_sort `Performed name, parse predicate))
  in
  let local_cells = typed_local_cells function_def.body in
  let reference_cells =
    typed_reference_arguments function_def
    |> List.map (fun (name, key, sort) -> (name, smt_identifier key, sort))
  in
  let state_cells =
    local_cells
    @ List.map
        (fun (name, key, sort) -> (name, smt_identifier key, sort))
        reference_cells
  in
  let state_expressions =
    List.map
      (fun (name, predicate) ->
        match List.find_opt (fun (cell, _, _) -> cell = name) state_cells with
        | Some (_, key, sort) ->
            (name, smt_identifier key, sort, parse predicate)
        | None ->
            typed_error_at contract.loc
              "state postcondition names unknown local cell `%s`" name)
      contract.state
  in
  let reference_names = List.map (fun (name, _, _) -> name) reference_cells in
  let validate_modified name =
    if not (List.mem name reference_names) then
      typed_error_at contract.loc
        "modifies footprint names non-reference parameter `%s`" name
  in
  List.iter validate_modified contract.modifies;
  List.iter
    (fun (kind, outcome, name) ->
      validate_modified name;
      if
        (kind = "raise" && not (List.mem_assoc outcome contract.raises))
        || (kind = "perform" && not (List.mem_assoc outcome contract.performs))
        || (kind <> "raise" && kind <> "perform")
      then
        typed_error_at contract.loc
          "outcome_modifies names undeclared outcome `%s:%s`" kind outcome)
    contract.outcome_modifies;
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
  let required_state_expressions =
    List.map
      (fun (name, predicate) ->
        match
          List.find_opt (fun (cell, _, _) -> cell = name) reference_cells
        with
        | Some (_, key, sort) ->
            (name, smt_identifier key, sort, parse predicate)
        | None ->
            typed_error_at contract.loc
              "requires_state names non-reference parameter `%s`" name)
      contract.requires_state
  in
  let outcome_state_expressions =
    List.map
      (fun (kind, outcome, name, predicate) ->
        let payload_sort =
          match kind with
          | "raise" ->
              if not (List.mem_assoc outcome contract.raises) then
                typed_error_at contract.loc
                  "outcome_state names undeclared raised outcome `%s`" outcome;
              payload_sort `Raised outcome
          | "perform" ->
              if not (List.mem_assoc outcome contract.performs) then
                typed_error_at contract.loc
                  "outcome_state names undeclared performed outcome `%s`"
                  outcome;
              payload_sort `Performed outcome
          | _ ->
              typed_error_at contract.loc
                "outcome_state kind must be `raise` or `perform`"
        in
        match List.find_opt (fun (cell, _, _) -> cell = name) state_cells with
        | Some (_, key, sort) ->
            ( kind,
              outcome,
              name,
              smt_identifier key,
              sort,
              payload_sort,
              parse predicate )
        | None ->
            typed_error_at contract.loc "outcome_state names unknown cell `%s`"
              name)
      contract.outcome_state
  in
  let state_names = List.map fst contract.state in
  if
    List.length state_names
    <> List.length (List.sort_uniq String.compare state_names)
  then typed_error_at contract.loc "state clauses must name each cell once";
  let names = List.map fst contract.raises in
  if List.length names <> List.length (List.sort_uniq String.compare names) then
    typed_error_at contract.loc "raises clauses must name each exception once";
  let operation_names = List.map fst contract.performs in
  if
    List.length operation_names
    <> List.length (List.sort_uniq String.compare operation_names)
  then
    typed_error_at contract.loc "performs clauses must name each operation once";
  let outcome_state_names =
    List.map
      (fun (kind, outcome, name, _) -> (kind, outcome, name))
      contract.outcome_state
  in
  if
    List.length outcome_state_names
    <> List.length (List.sort_uniq compare outcome_state_names)
  then
    typed_error_at contract.loc
      "outcome_state clauses must name each outcome cell once";
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
  let owned_paths = owned_result_paths "result" in
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
    typed_relational_expr program analysis Over function_def
      ~initial_state:
        (typed_initial_reference_state ~registry:program.registry function_def)
      env function_def.body
  in
  if owned_paths <> [] then
    use_returned_reference_theory generic_calls program.registry
      function_def.result;
  if generic_calls.summary_assumptions <> [] then
    typed_error_at contract.loc
      "effectful outcome summaries cannot use value-only assumptions";
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
        (("result", ("result", function_def.result)) :: formula_env)
        post_expression
    @ Option.fold ~none:[]
        ~some:(fun expression ->
          let content_sort = Option.get result_reference_sort in
          formula_theory_symbols program.registry
            (("value", ("result_state_value", content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression)
        result_state_expression
    @ List.concat_map
        (fun (path, expression, _fresh) ->
          formula_theory_symbols program.registry
            (( "identity",
               ("reachable_result_identity", reference_sort path.content_sort)
             )
            :: ("value", ("reachable_result_value", path.content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression)
        owned_result_expressions
    @ List.concat_map
        (fun (_, payload_sort, expression) ->
          let env =
            match payload_sort with
            | Some sort -> ("payload", ("payload", sort)) :: formula_env
            | None -> formula_env
          in
          formula_theory_symbols program.registry env expression)
        raised_expressions
    @ List.concat_map
        (fun (_, payload_sort, expression) ->
          let env =
            match payload_sort with
            | Some sort -> ("payload", ("payload", sort)) :: formula_env
            | None -> formula_env
          in
          formula_theory_symbols program.registry env expression)
        performed_expressions
    @ List.concat_map
        (fun (_, _, sort, expression) ->
          formula_theory_symbols program.registry
            (("value", ("state_value", sort))
            :: ("old", ("old_state_value", sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression)
        state_expressions
    @ List.concat_map
        (fun (_kind, _outcome, _name, _key, sort, payload_sort, expression) ->
          let env =
            ("value", ("state_value", sort))
            :: ("old", ("old_state_value", sort))
            :: formula_env
          in
          let env =
            match payload_sort with
            | Some payload_sort -> ("payload", ("payload", payload_sort)) :: env
            | None -> env
          in
          formula_theory_symbols program.registry env expression)
        outcome_state_expressions
    @ List.concat_map
        (fun (_, _, sort, expression) ->
          formula_theory_symbols program.registry
            (("value", ("initial_state_value", sort)) :: formula_env)
            expression)
        required_state_expressions
    |> List.sort_uniq String.compare
  in
  let program, _ = slice_program_theory program ~roots in
  let required_state_posts =
    List.map
      (fun (_name, key, sort, expression) ->
        let predicate =
          typed_formula program.registry
            (("value", ("initial_state_value", sort)) :: formula_env)
            expression
        in
        let initial_value = app "select" [ initial_heap_name sort; key ] in
        Printf.sprintf "(let ((initial_state_value %s)) %s)" initial_value
          predicate)
      required_state_expressions
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
  let post =
    typed_formula program.registry
      (("result", ("result", function_def.result)) :: formula_env)
      post_expression
  in
  let result_state_post =
    Option.map
      (fun expression ->
        let content_sort = Option.get result_reference_sort in
        ( content_sort,
          typed_formula program.registry
            (("value", ("result_state_value", content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression ))
      result_state_expression
  in
  let owned_result_posts =
    List.map
      (fun (path, expression, fresh) ->
        ( path.path,
          path.content_sort,
          typed_formula program.registry
            (( "identity",
               ("reachable_result_identity", reference_sort path.content_sort)
             )
            :: ("value", ("reachable_result_value", path.content_sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression,
          fresh ))
      owned_result_expressions
  in
  let raised =
    List.map
      (fun (name, payload_sort, expression) ->
        let env =
          match payload_sort with
          | Some sort -> ("payload", ("payload", sort)) :: formula_env
          | None -> formula_env
        in
        (name, payload_sort, typed_formula program.registry env expression))
      raised_expressions
  in
  let performed =
    List.map
      (fun (name, payload_sort, expression) ->
        let env =
          match payload_sort with
          | Some sort -> ("payload", ("payload", sort)) :: formula_env
          | None -> formula_env
        in
        (name, payload_sort, typed_formula program.registry env expression))
      performed_expressions
  in
  let state_posts =
    List.map
      (fun (name, key, sort, expression) ->
        ( name,
          key,
          sort,
          typed_formula program.registry
            (("value", ("state_value", sort))
            :: ("old", ("old_state_value", sort))
            :: ("result", ("result", function_def.result))
            :: formula_env)
            expression ))
      state_expressions
  in
  let outcome_state_posts =
    List.map
      (fun (kind, outcome, name, key, sort, payload_sort, expression) ->
        let env =
          ("value", ("state_value", sort))
          :: ("old", ("old_state_value", sort))
          :: formula_env
        in
        let env =
          match payload_sort with
          | Some payload_sort -> ("payload", ("payload", payload_sort)) :: env
          | None -> env
        in
        ( kind,
          outcome,
          name,
          key,
          sort,
          payload_sort,
          typed_formula program.registry env expression ))
      outcome_state_expressions
  in
  let bind_payload payload_sort payload predicate =
    match (payload_sort, payload) with
    | None, _ -> predicate
    | Some _, Some payload ->
        Printf.sprintf "(let ((payload %s)) %s)" payload predicate
    | Some _, None -> "false"
  in
  let initial_cell_value initial key sort =
    match List.assoc_opt key generic_calls.local_initial_values with
    | Some value -> value
    | None -> heap_select initial key sort
  in
  let abnormal_state kind outcome payload initial final =
    outcome_state_posts
    |> List.filter_map
         (fun
           (candidate_kind, candidate, _name, key, sort, payload_sort, predicate)
         ->
           if candidate_kind <> kind || candidate <> outcome then None
           else
             let value = heap_select final key sort in
             let old = initial_cell_value initial key sort in
             Some
               (bind_payload payload_sort payload
                  (Printf.sprintf
                     "(let ((state_value %s) (old_state_value %s)) %s)" value
                     old predicate)))
  in
  let obligation =
    Relational_outcome.safety_obligation ~pre
      ~normal:(fun ~value ~initial ~final ->
        let state_obligations =
          List.map
            (fun (_name, key, sort, predicate) ->
              let state_value = heap_select final key sort in
              let old_state = initial_cell_value initial key sort in
              Printf.sprintf
                "(let ((result %s) (state_value %s) (old_state_value %s)) %s)"
                value state_value old_state predicate)
            state_posts
        in
        let result_obligations =
          match result_state_post with
          | None -> []
          | Some (content_sort, predicate) ->
              let content = heap_select final value content_sort in
              let state =
                Printf.sprintf "(let ((result %s) (result_state_value %s)) %s)"
                  value content predicate
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
              state :: freshness
        in
        let owned_result_obligations =
          let paths = owned_result_paths value in
          List.concat_map
            (fun (path_name, content_sort, predicate, fresh) ->
              let path = List.find (fun path -> path.path = path_name) paths in
              let content = heap_select final path.identity content_sort in
              let state =
                Printf.sprintf
                  "(let ((result %s) (reachable_result_identity %s) \
                   (reachable_result_value %s)) %s)"
                  value path.identity content predicate
              in
              let obligations = [ app "=>" [ path.guard; state ] ] in
              if not fresh then
                let identities =
                  reference_cells
                  |> List.filter_map (fun (_name, identity, sort) ->
                      if typed_smt_sort sort = typed_smt_sort content_sort then
                        Some identity
                      else None)
                in
                let borrowed_from_entry =
                  app "=>"
                    [
                      path.guard;
                      or_
                        (List.map
                           (fun identity -> app "=" [ path.identity; identity ])
                           identities);
                    ]
                in
                borrowed_from_entry :: obligations
              else
                let identities =
                  List.map (fun (_, identity, _) -> identity) reference_cells
                in
                match identities with
                | [] -> obligations
                | identities ->
                    app "=>"
                      [
                        path.guard; app "distinct" (path.identity :: identities);
                      ]
                    :: obligations)
            owned_result_posts
        in
        let owned_result_distinctness =
          let paths = owned_result_paths value in
          owned_result_posts
          |> List.filter_map (fun (path_name, _sort, _predicate, fresh) ->
              if not fresh then None
              else
                let path =
                  List.find (fun path -> path.path = path_name) paths
                in
                Some (path.identity, path.content_sort, path.guard))
          |> guarded_identity_distinctness
        in
        let obligations =
          (post :: state_obligations)
          @ result_obligations @ owned_result_obligations
          @ owned_result_distinctness
          @ frame_obligations ~initial ~final ~references:reference_cells
              ~modified:
                (reference_modified_identities reference_cells
                   normal_modified_names)
        in
        Printf.sprintf "(let ((result %s)) %s)" value (and_ obligations))
      ~raised:(fun ~exception_ ~payload ~initial ~final ->
        let post =
          match
            List.find_opt (fun (name, _, _) -> name = exception_) raised
          with
          | Some (_, payload_sort, predicate) ->
              bind_payload payload_sort payload predicate
          | None -> "false"
        in
        and_
          ((post :: abnormal_state "raise" exception_ payload initial final)
          @ frame_obligations ~initial ~final ~references:reference_cells
              ~modified:
                (reference_modified_identities reference_cells
                   (outcome_modified_names "raise" exception_))))
      ~performed:(fun ~operation ~payload ~continuation:_ ~initial ~final ->
        let post =
          match
            List.find_opt (fun (name, _, _) -> name = operation) performed
          with
          | Some (_, payload_sort, predicate) ->
              bind_payload payload_sort payload predicate
          | None -> "false"
        in
        and_
          ((post :: abnormal_state "perform" operation payload initial final)
          @ frame_obligations ~initial ~final ~references:reference_cells
              ~modified:
                (reference_modified_identities reference_cells
                   (outcome_modified_names "perform" operation))))
      relation
  in
  let obligation =
    match generic_calls.side_conditions with
    | [] -> obligation
    | conditions ->
        and_ [ app "=>" [ pre; and_ (List.rev conditions) ]; obligation ]
  in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer
    "(set-option :produce-models true)\n(set-logic ALL)\n";
  Buffer.add_string buffer
    (typed_datatype_prelude ~extra_sorts:(List.map snd choices) program
       function_def);
  List.iter
    (fun (symbol, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n"
           (smt_identifier symbol.Typed_core.key)
           (typed_smt_sort sort)))
    function_def.arguments;
  List.iter
    (fun (key, _heap) ->
      let sort =
        typed_function_reference_sorts ~registry:program.registry function_def
        |> List.find_opt (fun sort -> heap_key sort = key)
        |> Option.get
      in
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s (Array %s %s))\n"
           (initial_heap_name sort)
           (typed_smt_sort (reference_sort sort))
           (typed_smt_sort sort)))
    (typed_initial_reference_state ~registry:program.registry function_def);
  List.iter
    (fun (name, sort) ->
      Buffer.add_string buffer
        (Printf.sprintf "(declare-const %s %s)\n" name (typed_smt_sort sort)))
    choices;
  List.iter
    (fun assumption ->
      Buffer.add_string buffer (Printf.sprintf "(assert %s)\n" assumption))
    (List.rev generic_calls.semantic_assumptions);
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
