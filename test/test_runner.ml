open Refined_core

let contains text fragment =
  let text_length = String.length text in
  let fragment_length = String.length fragment in
  let rec search index =
    index + fragment_length <= text_length
    &&
    if String.sub text index fragment_length = fragment then true
    else search (index + 1)
  in
  fragment_length = 0 || search 0

let require expected obligation =
  match (expected, solve obligation) with
  | `Valid, Valid | `Invalid, Invalid _ -> ()
  | `Valid, (Invalid _ | Unknown _) ->
      Alcotest.failf "%s should be valid" obligation.name
  | `Invalid, (Valid | Unknown _) ->
      Alcotest.failf "%s should be invalid" obligation.name

let test_sha256 () =
  Alcotest.check Alcotest.string "SHA-256 abc vector"
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    (proof_digest "abc")

let test_compositional_judgment () =
  let module Typing = Refined_ir.Typing_judgment in
  let left =
    Typing.Safety.synthesize ~rule:Constant ~predicate:"left" ~children:[]
  in
  let right =
    Typing.Safety.synthesize ~rule:Constant ~predicate:"right" ~children:[]
  in
  let branch =
    Typing.Safety.branch ~guard:"guard" ~if_true:left ~if_false:right
  in
  if
    Typing.Safety.predicate branch
    <> "(or (and guard left) (and (not guard) right))"
  then failwith "branch refinements were not composed structurally";
  if Typing.Safety.derivation branch <> [ Branch; Constant; Constant ] then
    failwith "typing derivation did not retain syntax-directed rules";
  let safety =
    Typing.Safety.check ~assumptions:[ "pre" ] ~expected:"post" left
    |> Typing.Safety.obligation
  in
  if safety <> "(=> (and pre left) post)" then
    failwith "safety subsumption has the wrong direction";
  let coverage_left =
    Typing.Coverage.synthesize ~rule:Constant ~predicate:"left" ~children:[]
  in
  let coverage =
    Typing.Coverage.check ~assumptions:[ "pre" ] ~expected:"post" coverage_left
    |> Typing.Coverage.obligation
  in
  if coverage <> "(=> post (and pre left))" then
    failwith "coverage subsumption has the wrong direction"

let test_hindley_evars () =
  let module Term = struct
    type head = Atom | List
    type t = Variable of string | Node of head * t list

    let view = function
      | Variable variable -> `Variable variable
      | Node (head, children) -> `Node (head, children)

    let make_node head children = Node (head, children)
    let equal_head = ( = )
    let equal = ( = )
  end in
  let module Evars = Refined_ir.Evar_context.Make (Term) in
  let context = Evars.create () in
  let formal = Term.Node (List, [ Variable "element" ]) in
  let actual = Term.Node (List, [ Node (Atom, []) ]) in
  (match Evars.unify context ~formal ~actual with
  | Ok () -> ()
  | Error _ -> failwith "value-dependent evar did not unify at the call site");
  if Evars.substitute context formal <> actual then
    failwith "Hindley substitution was not applied recursively";
  if not (Evars.is_complete context ~variables:[ "element" ]) then
    failwith "solved Hindley evar context was reported as incomplete";
  let cyclic = Evars.create () in
  match
    Evars.unify cyclic ~formal:(Term.Variable "a")
      ~actual:(Term.Node (List, [ Variable "a" ]))
  with
  | Error (Occurs _) -> ()
  | Ok () | Error (Shape_mismatch _) ->
      failwith "Hindley evar occurs-check did not reject a cyclic solution"

let test_higher_sorted_hindley_application () =
  let open Refined_ir.Generic_refinement in
  let int_sort = Base Int in
  let predicate_sort = Arrow (int_sort, Base Bool) in
  let indexed predicate =
    Refined
      {
        base = "IntPredicate";
        index_sort = predicate_sort;
        index = predicate;
        predicate = Boolean true;
      }
  in
  let positive =
    Lambda ("value", int_sort, Greater (Variable "value", Integer 0))
  in
  let negated =
    Lambda
      ("value", int_sort, Not (Apply (Generic "property", Variable "value")))
  in
  let scheme =
    Forall
      ( { name = "property"; mode = Hindley; sort = predicate_sort },
        Mono (Function (indexed (Generic "property"), indexed negated)) )
  in
  (match elaborate_application scheme [ indexed positive ] with
  | Error _ -> failwith "higher-sorted Hindley application did not elaborate"
  | Ok elaboration ->
      if
        elaboration.instantiations
        <> [ { generic = "property"; refinement = positive } ]
      then failwith "ghost refinement instantiation was not synthesized";
      let expected_result =
        indexed
          (Lambda
             ("value", int_sort, Not (Greater (Variable "value", Integer 0))))
      in
      if elaboration.result <> expected_result then
        failwith "Hindley instantiation was not substituted and beta-reduced";
      if List.length elaboration.constraints <> 1 then
        failwith "application checking did not retain argument constraints");
  let output_only =
    Forall
      ( { name = "property"; mode = Hindley; sort = predicate_sort },
        Mono
          (Function
             ( Refined
                 {
                   base = "int";
                   index_sort = int_sort;
                   index = Integer 0;
                   predicate = Boolean true;
                 },
               indexed (Generic "property") )) )
  in
  (match well_formed output_only with
  | Error (Ill_formed_hindley "property") -> ()
  | Ok () | Error _ ->
      failwith "output-only Hindley generic was accepted as value-dependent");
  let horn_refined predicate =
    Refined
      { base = "int"; index_sort = int_sort; index = Integer 1; predicate }
  in
  let horn_application = Apply (Generic "property", Integer 1) in
  let horn =
    Forall
      ( { name = "property"; mode = Horn; sort = predicate_sort },
        Mono
          (Function
             (horn_refined horn_application, horn_refined horn_application)) )
  in
  (match
     elaborate_application horn
       [ horn_refined (Greater (Integer 1, Integer 0)) ]
   with
  | Error _ -> failwith "positive Horn generic was not solved"
  | Ok elaboration ->
      let expected =
        Lambda
          ( "horn_property",
            int_sort,
            Greater (Variable "horn_property", Integer 0) )
      in
      if
        not
          (List.exists
             (fun instantiation ->
               instantiation.generic = "property"
               && instantiation.refinement = expected)
             elaboration.instantiations)
      then failwith "Horn lower bound did not produce the expected predicate");
  let negative_horn =
    Forall
      ( { name = "property"; mode = Horn; sort = predicate_sort },
        Mono
          (Function
             ( horn_refined (Or [ horn_application; Boolean true ]),
               horn_refined horn_application )) )
  in
  match well_formed negative_horn with
  | Error (Ill_formed_horn "property") -> ()
  | Ok () | Error _ ->
      failwith "Horn generic under disjunction passed positivity checking"

let test_mutually_recursive_horn_fixpoint () =
  let module Term = struct
    type parameter = string

    type t =
      | False
      | True
      | Reference of string
      | Or of t list
      | Lambda of string * t
      | Grow of t

    let falsity = False

    let rec normalize = function
      | Or terms -> (
          let terms =
            terms |> List.map normalize
            |> List.concat_map (function
              | Or nested -> nested
              | term -> [ term ])
            |> List.filter (( <> ) False)
            |> List.sort_uniq compare
          in
          if List.mem True terms then True
          else
            match terms with
            | [] -> False
            | [ term ] -> term
            | terms -> Or terms)
      | Lambda (parameter, body) -> Lambda (parameter, normalize body)
      | Grow term -> Grow (normalize term)
      | (False | True | Reference _) as term -> term

    let join terms = normalize (Or terms)
    let lambda ~parameter body = Lambda (parameter, normalize body)

    let rec instantiate solutions = function
      | Reference name -> (
          match List.assoc_opt name solutions with
          | Some (Lambda (_, body)) -> body
          | Some body -> body
          | None -> Reference name)
      | Or terms -> Or (List.map (instantiate solutions) terms) |> normalize
      | Lambda (parameter, body) ->
          Lambda (parameter, instantiate solutions body)
      | Grow term -> Grow (instantiate solutions term)
      | (False | True) as term -> term

    let abstract ~argument:_ ~parameter:_ body = body

    let rec dependencies ~variables = function
      | Reference name when List.mem name variables -> [ name ]
      | Or terms -> List.concat_map (dependencies ~variables) terms
      | Lambda (_, body) | Grow body -> dependencies ~variables body
      | False | True | Reference _ -> []

    let equal left right = normalize left = normalize right
  end in
  let module Solver = Refined_ir.Horn_fixpoint.Make (Term) in
  let variables =
    [
      Solver.{ name = "P"; parameter = "p" };
      Solver.{ name = "Q"; parameter = "q" };
    ]
  in
  let clauses =
    [
      Solver.{ head = "P"; argument = Term.True; body = Term.True };
      Solver.{ head = "P"; argument = Term.True; body = Term.Reference "Q" };
      Solver.{ head = "Q"; argument = Term.True; body = Term.Reference "P" };
    ]
  in
  (match Solver.solve ~variables ~clauses () with
  | Error _ -> failwith "mutually-recursive Horn SCC did not converge"
  | Ok solution ->
      if
        solution.predicates
        <> [ ("P", Term.Lambda ("p", True)); ("Q", Lambda ("q", True)) ]
      then failwith "base fact did not propagate through recursive Horn SCC";
      if
        not
          (List.exists
             (fun component ->
               List.sort String.compare component = [ "P"; "Q" ])
             solution.strongly_connected_components)
      then failwith "Horn dependency graph lost its recursive SCC");
  let cycle_only =
    [
      Solver.{ head = "P"; argument = Term.True; body = Term.Reference "Q" };
      Solver.{ head = "Q"; argument = Term.True; body = Term.Reference "P" };
    ]
  in
  (match Solver.solve ~variables ~clauses:cycle_only () with
  | Error _ -> failwith "bottom recursive Horn SCC did not stabilize"
  | Ok solution ->
      if
        solution.predicates
        <> [ ("P", Term.Lambda ("p", False)); ("Q", Lambda ("q", False)) ]
      then failwith "least Horn solution for an unfounded cycle was not false");
  let growing =
    [
      Solver.
        { head = "P"; argument = Term.True; body = Term.Grow (Reference "P") };
    ]
  in
  match
    Solver.solve ~max_iterations:4
      ~variables:[ List.hd variables ]
      ~clauses:growing ()
  with
  | Error (Did_not_converge 4) -> ()
  | Ok _ | Error _ -> failwith "non-converging Horn recursion was accepted"

let test_relational_outcomes () =
  let module R = Refined_ir.Relational_outcome in
  let state = [ ("cell", "old") ] in
  let updated =
    R.bind (R.write ~state ~cell:"cell" ~value:"new") (fun _ state ->
        R.read ~state ~cell:"cell")
  in
  (match updated with
  | [ { initial_state; final_state; outcome = Return "new"; _ } ] ->
      if initial_state <> state || List.assoc "cell" final_state <> "new" then
        failwith "relational bind did not thread state"
  | _ -> failwith "relational state update/read produced the wrong paths");
  let continued = ref false in
  let abnormal =
    R.bind
      (R.branch ~condition:"c" ~if_true:(R.raise_ ~state "E")
         ~if_false:(R.perform ~state ~operation:"Choose" ~payload:"p" ()))
      (fun _ _ ->
        continued := true;
        R.return ~state "impossible")
  in
  if !continued then failwith "relational bind continued an abnormal outcome";
  if
    not
      (List.exists
         (fun path ->
           path.R.outcome = Raised { exception_ = "E"; payload = None })
         abnormal
      && List.exists
           (fun path ->
             path.R.outcome
             = Performed
                 {
                   operation = "Choose";
                   payload = Some "p";
                   continuation = None;
                 })
           abnormal)
  then failwith "branch lost raised/performed outcomes";
  let handled =
    R.handle_effect ~operation:"Choose"
      (R.try_with abnormal (fun ~exception_ ~payload:_ ~state ->
           R.return ~state ("caught_" ^ exception_)))
      (fun ~payload ~continuation:_ ~state ->
        R.return ~state ("handled_" ^ Option.get payload))
  in
  if
    not
      (List.for_all
         (fun path ->
           match path.R.outcome with
           | Return ("caught_E" | "handled_p") -> true
           | Return _ | Raised _ | Performed _ -> false)
         handled)
  then failwith "relational handlers did not discharge matching outcomes";
  let safety =
    R.safety_obligation ~pre:"pre"
      ~normal:(fun ~value ~initial:_ ~final:_ -> "normal_" ^ value)
      ~raised:(fun ~exception_ ~payload:_ ~initial:_ ~final:_ ->
        "raised_" ^ exception_)
      ~performed:(fun ~operation ~payload ~continuation:_ ~initial:_ ~final:_ ->
        operation ^ "_" ^ Option.get payload)
      abnormal
  in
  if not (contains safety "raised_E" && contains safety "Choose_p") then
    failwith "relational safety omitted abnormal postconditions";
  let coverage =
    R.coverage_obligation ~target:"target"
      ~matches:(fun path ->
        match path.R.outcome with
        | Raised { exception_ = "E"; _ } -> "wanted"
        | _ -> "false")
      abnormal
  in
  if not (contains coverage "wanted") then
    failwith "relational coverage omitted a reachable outcome"

let integration_suite () =
  let compile source output =
    let command =
      Printf.sprintf "ocamlc -bin-annot -c %s -o %s.cmo" (Filename.quote source)
        (Filename.quote output)
    in
    if Sys.command command <> 0 then failwith ("failed to compile " ^ source)
  in
  compile "../examples/valid.ml" "typed_valid";
  compile "../examples/invalid.ml" "typed_invalid";
  compile "../examples/theory.ml" "typed_theory";
  compile "../examples/theory_missing.ml" "typed_theory_missing";
  compile "../examples/choice.ml" "typed_choice";
  compile "../examples/choice_incomplete.ml" "typed_choice_incomplete";
  compile "../examples/polymorphic.ml" "typed_polymorphic";
  compile "../examples/tuple.ml" "typed_tuple";
  compile "../examples/unsupported.ml" "typed_unsupported";
  compile "../examples/recursive_valid.ml" "typed_recursive_valid";
  compile "../examples/recursive_bad_measure.ml" "typed_recursive_bad_measure";
  compile "../examples/recursive_missing_measure.ml"
    "typed_recursive_missing_measure";
  compile "../examples/recursive_missing_summary.ml"
    "typed_recursive_missing_summary";
  compile "../examples/recursive_coverage.ml" "typed_recursive_coverage";
  compile "../examples/mutual_recursive.ml" "typed_mutual_recursive";
  compile "../examples/parameterized_adt.ml" "typed_parameterized_adt";
  compile "../examples/open_parameterized_adt.ml" "typed_open_parameterized_adt";
  compile "../examples/logic_disambiguation.ml" "typed_logic_disambiguation";
  compile "../examples/logic_disambiguation_invalid.ml"
    "typed_logic_disambiguation_invalid";
  compile "../examples/logic_ambiguity_invalid.ml"
    "typed_logic_ambiguity_invalid";
  compile "../examples/coverage_composition.ml" "typed_coverage_composition";
  compile "../examples/coverage_bad_witness.ml" "typed_coverage_bad_witness";
  compile "../examples/coverage_incomplete_witness.ml"
    "typed_coverage_incomplete_witness";
  compile "../examples/exception_valid.ml" "typed_exception_valid";
  compile "../examples/exception_invalid.ml" "typed_exception_invalid";
  compile "../examples/exception_coverage.ml" "typed_exception_coverage";
  compile "../examples/state_valid.ml" "typed_state_valid";
  compile "../examples/state_invalid.ml" "typed_state_invalid";
  compile "../examples/state_escape.ml" "typed_state_escape";
  compile "../examples/state_unknown_contract.ml" "typed_state_unknown_contract";
  compile "../examples/effect_valid.ml" "typed_effect_valid";
  compile "../examples/effect_invalid.ml" "typed_effect_invalid";
  compile "../examples/effect_resume.ml" "typed_effect_resume";
  compile "../examples/payload_outcomes.ml" "typed_payload_outcomes";
  compile "../examples/payload_outcomes_invalid.ml"
    "typed_payload_outcomes_invalid";
  compile "../examples/outcome_calls.ml" "typed_outcome_calls";
  compile "../examples/outcome_recursive_unsupported.ml"
    "typed_outcome_recursive_unsupported";
  compile "../examples/outcome_recursive_coverage.ml"
    "typed_outcome_recursive_coverage";
  compile "../examples/outcome_recursive_missing_measure.ml"
    "typed_outcome_recursive_missing_measure";
  compile "../examples/reference_state.ml" "typed_reference_state";
  compile "../examples/reference_state_invalid.ml"
    "typed_reference_state_invalid";
  compile "../examples/reference_state_alias.ml" "typed_reference_state_alias";
  compile "../examples/reference_fresh.ml" "typed_reference_fresh";
  compile "../examples/nondeterministic_state.ml" "typed_nondeterministic_state";
  compile "../examples/nondeterministic_state_invalid.ml"
    "typed_nondeterministic_state_invalid";
  compile "../examples/abnormal_state.ml" "typed_abnormal_state";
  compile "../examples/abnormal_state_invalid.ml" "typed_abnormal_state_invalid";
  compile "../examples/relational_witness.ml" "typed_relational_witness";
  compile "../examples/relational_witness_invalid.ml"
    "typed_relational_witness_invalid";
  compile "../examples/typed_ghost_frame.ml" "typed_ghost_frame";
  compile "../examples/typed_ghost_frame_invalid.ml" "typed_ghost_frame_invalid";
  compile "../examples/reference_escape.ml" "typed_reference_escape";
  compile "../examples/reference_escape_invalid.ml"
    "typed_reference_escape_invalid";
  compile "../examples/reference_escape_missing_state.ml"
    "typed_reference_escape_missing_state";
  compile "../examples/reference_escape_nested.ml"
    "typed_reference_escape_nested";
  compile "../examples/physical_equality_invalid.ml"
    "typed_physical_equality_invalid";
  compile "../examples/reachable_heap.ml" "typed_reachable_heap";
  compile "../examples/reachable_heap_invalid.ml" "typed_reachable_heap_invalid";
  compile "../examples/reachable_heap_incomplete.ml"
    "typed_reachable_heap_incomplete";
  compile "../examples/reachable_heap_recursive.ml"
    "typed_reachable_heap_recursive";
  compile "../examples/recursive_ownership.ml" "typed_recursive_ownership";
  compile "../examples/recursive_ownership_bad_permission.ml"
    "typed_recursive_ownership_bad_permission";
  compile "../examples/recursive_ownership_linear_invalid.ml"
    "typed_recursive_ownership_linear_invalid";
  compile "../examples/recursive_ownership_alias_invalid.ml"
    "typed_recursive_ownership_alias_invalid";
  compile "../examples/recursive_ownership_bad_tail.ml"
    "typed_recursive_ownership_bad_tail";
  compile "../examples/conditional_resume.ml" "typed_conditional_resume";
  compile "../examples/multishot_unsupported.ml" "typed_multishot_unsupported";
  compile "../examples/outcome_coverage.ml" "typed_outcome_coverage";
  compile "../examples/outcome_coverage_invalid.ml"
    "typed_outcome_coverage_invalid";
  compile "../examples/outcome_coverage_incomplete.ml"
    "typed_outcome_coverage_incomplete";
  obligations_of_cmt "typed_valid.cmt" |> List.iter (require `Valid);
  obligations_of_cmt "typed_invalid.cmt" |> List.iter (require `Invalid);
  obligations_of_cmt "typed_theory.cmt"
  |> List.iter (fun obligation ->
      if obligation.trusted_axioms <> [ "ListTheory.hd_mem" ] then
        failwith "local module axiom provenance was not preserved";
      require `Valid obligation);
  obligations_of_cmt "typed_theory_missing.cmt" |> List.iter (require `Invalid);
  obligations_of_cmt "typed_choice.cmt" |> List.iter (require `Valid);
  obligations_of_cmt "typed_polymorphic.cmt" |> List.iter (require `Valid);
  obligations_of_cmt "typed_tuple.cmt" |> List.iter (require `Valid);
  obligations_of_cmt "typed_recursive_valid.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "call_result_") then
        failwith "recursive call did not use its function summary";
      if not (contains obligation.smt "(<") then
        failwith "recursive call did not emit a decreasing-measure obligation";
      require `Valid obligation);
  obligations_of_cmt "typed_mutual_recursive.cmt" |> List.iter (require `Valid);
  obligations_of_cmt "typed_parameterized_adt.cmt"
  |> List.iter (fun obligation ->
      let has_box = contains obligation.smt "T_box_" in
      let has_int_box = has_box && contains obligation.smt "_Int" in
      let has_bool_box = has_box && contains obligation.smt "_Bool" in
      (match obligation.name with
      | "int_box" | "int_roundtrip" ->
          if (not has_int_box) || has_bool_box then
            failwith "int box obligation was not monomorphised in isolation"
      | "bool_box" ->
          if (not has_bool_box) || has_int_box then
            failwith "bool box obligation was not monomorphised in isolation"
      | "both_boxes" ->
          if not (has_int_box && has_bool_box) then
            failwith "two concrete instances were not emitted together"
      | "opaque_box" ->
          if not has_int_box then failwith "opaque ADT sort was not declared";
          if contains obligation.smt "(declare-fun C_" then
            failwith "opaque ADT flow emitted an unused constructor bundle"
      | "int_cell" ->
          if
            not
              (contains obligation.smt "T_cell_"
              && contains obligation.smt "_Int")
          then failwith "parameterized record was not monomorphised"
      | "bool_cell_roundtrip" ->
          if
            not
              (contains obligation.smt "T_cell_"
              && contains obligation.smt "_Bool")
          then failwith "polymorphic record helper was not instantiated"
      | "int_tree" ->
          if
            not
              (contains obligation.smt "T_tree_"
              && contains obligation.smt "_Int")
          then failwith "recursive parameterized ADT was not monomorphised"
      | name -> failwith ("unexpected parameterized ADT obligation " ^ name));
      require `Valid obligation);
  (match obligations_of_cmt "typed_open_parameterized_adt.cmt" with
  | _ -> failwith "an open parameterized ADT obligation was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_logic_disambiguation.cmt"
  |> List.iter (fun obligation ->
      if contains obligation.smt "Tvar_" then
        failwith "typed logic elaboration leaked an open ADT sort";
      (match obligation.name with
      | "mixed_box" | "reversed_box" ->
          if
            not
              (contains obligation.smt "T_box_"
              && contains obligation.smt "_Int"
              && contains obligation.smt "_Bool")
          then
            failwith "constructor expected sort did not select both instances"
      | "mixed_nothing" | "reversed_nothing" ->
          if
            not
              (contains obligation.smt "T_maybe_"
              && contains obligation.smt "_Int"
              && contains obligation.smt "_Bool")
          then failwith "nullary constructor was not resolved by result sort"
      | "mixed_fields" ->
          if
            not
              (contains obligation.smt "T_cell_"
              && contains obligation.smt "_Int"
              && contains obligation.smt "_Bool")
          then failwith "record selector was not resolved from receiver sort"
      | name -> failwith ("unexpected typed logic obligation " ^ name));
      require `Valid obligation);
  (match obligations_of_cmt "typed_logic_disambiguation_invalid.cmt" with
  | _ ->
      failwith "constructor argument with the wrong expected sort was accepted"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_logic_ambiguity_invalid.cmt" with
  | _ -> failwith "constructor without an expected sort was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_coverage_composition.cmt"
  |> List.iter (fun obligation ->
      if
        obligation.name = "successor_twice"
        && not (contains obligation.smt "call_result_")
      then failwith "coverage call chain did not use constructive summaries";
      if obligation.name = "countdown" && not (contains obligation.smt "(<")
      then failwith "recursive coverage did not retain its measure constraint";
      require `Valid obligation);
  obligations_of_cmt "typed_coverage_bad_witness.cmt"
  |> List.iter (require `Invalid);
  (match obligations_of_cmt "typed_coverage_incomplete_witness.cmt" with
  | _ -> failwith "incomplete coverage witnesses were accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_exception_valid.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "(=>") then
        failwith "exception relation did not emit guarded path obligations";
      require `Valid obligation);
  obligations_of_cmt "typed_exception_invalid.cmt"
  |> List.iter (require `Invalid);
  obligations_of_cmt "typed_exception_coverage.cmt"
  |> List.iter (require `Invalid);
  obligations_of_cmt "typed_state_valid.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "state_value") then
        failwith "state contract did not reach the relational VC";
      require `Valid obligation);
  obligations_of_cmt "typed_state_invalid.cmt" |> List.iter (require `Invalid);
  obligations_of_cmt "typed_state_escape.cmt" |> List.iter (require `Valid);
  (match obligations_of_cmt "typed_state_unknown_contract.cmt" with
  | _ -> failwith "state contract naming an unknown cell was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_effect_valid.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "(=>") then
        failwith "performed outcome did not emit a guarded obligation";
      require `Valid obligation);
  obligations_of_cmt "typed_effect_invalid.cmt" |> List.iter (require `Invalid);
  obligations_of_cmt "typed_effect_resume.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "42") then
        failwith "resumed continuation result did not reach the VC";
      require `Valid obligation);
  obligations_of_cmt "typed_payload_outcomes.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "payload_raise"
        || obligation.name = "payload_perform")
        && not (contains obligation.smt "payload")
      then failwith "payload outcome did not reach the VC";
      require `Valid obligation);
  obligations_of_cmt "typed_payload_outcomes_invalid.cmt"
  |> List.iter (require `Invalid);
  obligations_of_cmt "typed_outcome_calls.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "catches_call" || obligation.name = "handles_call")
        && not (contains obligation.smt "call_result_")
      then failwith "effectful call did not use its outcome summary";
      require `Valid obligation);
  obligations_of_cmt "typed_outcome_recursive_unsupported.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "(<") then
        failwith "recursive outcome safety omitted its measure";
      require `Valid obligation);
  obligations_of_cmt "typed_outcome_recursive_coverage.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "(<") then
        failwith "recursive outcome coverage omitted its measure";
      require `Valid obligation);
  (match obligations_of_cmt "typed_outcome_recursive_missing_measure.cmt" with
  | _ -> failwith "recursive outcome without a measure was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_outcome_coverage.cmt"
  |> List.iter (fun obligation ->
      if
        obligation.name = "mapped_outcome"
        && not (contains obligation.smt "call_payload_")
      then failwith "under outcome call summary was not composed";
      require `Valid obligation);
  obligations_of_cmt "typed_outcome_coverage_invalid.cmt"
  |> List.iter (require `Invalid);
  (match obligations_of_cmt "typed_outcome_coverage_incomplete.cmt" with
  | _ -> failwith "incomplete outcome witnesses were accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_reference_state.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "initial_") then
        failwith "reference state did not expose its initial value";
      if
        (obligation.name = "safety_wrapper"
        || obligation.name = "coverage_wrapper")
        && not (contains obligation.smt "call_state_")
      then failwith "cross-function state summary was not composed";
      require `Valid obligation);
  obligations_of_cmt "typed_reference_state_invalid.cmt"
  |> List.iter (require `Invalid);
  obligations_of_cmt "typed_reference_state_alias.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "aliased" || obligation.name = "aliased_coverage")
        && not
             (contains obligation.smt "(=> (="
             || contains obligation.smt "(=> (and")
      then failwith "aliased reference summary lost consistency guard";
      require `Valid obligation);
  obligations_of_cmt "typed_reference_fresh.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "(distinct ref_") then
        failwith "dynamic allocations lost freshness";
      require `Valid obligation);
  obligations_of_cmt "typed_nondeterministic_state.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "(store") then
        failwith "nondeterministic state paths lost their heaps";
      if
        obligation.name = "nondeterministic_outcome"
        && not (contains obligation.smt " 3" && contains obligation.smt " 4")
      then failwith "nondeterministic outcome paths were not both retained";
      require `Valid obligation);
  obligations_of_cmt "typed_nondeterministic_state_invalid.cmt"
  |> List.iter (require `Invalid);
  obligations_of_cmt "typed_abnormal_state.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "catches_abnormal_state"
        || obligation.name = "handles_abnormal_state")
        && not (contains obligation.smt "call_outcome_state_")
      then failwith "abnormal state summary did not update caller heap";
      if
        obligation.name = "abnormal_write"
        && obligation.mode = Under
        && not (contains obligation.smt "missing_outcome_state_")
      then failwith "abnormal state summary did not update caller heap";
      require `Valid obligation);
  obligations_of_cmt "typed_abnormal_state_invalid.cmt"
  |> List.iter (require `Invalid);
  obligations_of_cmt "typed_relational_witness.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "absolute_wrapper"
        || obligation.name = "ghost_wrapper"
        || obligation.name = "relational_bump_wrapper")
        && not (contains obligation.smt "call_result_")
      then failwith "relational witness summary was not composed";
      if
        obligation.name = "ghost_successor"
        && not (contains obligation.smt "coverage_ghost_")
      then failwith "coverage ghost was not existentially synthesized";
      if
        obligation.name = "ghost_wrapper"
        && not (contains obligation.smt "call_ghost_")
      then failwith "relational ghost was not composed at the call site";
      if
        (obligation.name = "relational_bump"
        || obligation.name = "relational_bump_wrapper")
        && not (contains obligation.smt "select initial_heap")
      then failwith "relational witness lost its initial heap binding";
      require `Valid obligation);
  obligations_of_cmt "typed_relational_witness_invalid.cmt"
  |> List.iter (require `Invalid);
  obligations_of_cmt "typed_ghost_frame.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "adt_ghost" || obligation.name = "adt_ghost_wrapper")
        && not (contains obligation.smt "token" && contains obligation.smt "Int")
      then failwith "typed ADT ghost was not monomorphized";
      if
        (obligation.name = "framed_write" || obligation.name = "framed_raise")
        && not (contains obligation.smt "initial_heap_Bool")
      then failwith "heap frame obligation was not emitted";
      require `Valid obligation);
  obligations_of_cmt "typed_ghost_frame_invalid.cmt"
  |> List.iter (fun obligation ->
      if obligation.name = "havoc" then require `Valid obligation
      else (
        if
          obligation.name = "missing_call_frame"
          && not (contains obligation.smt "call_state_")
        then failwith "safety modifies footprint was not havoced at call site";
        require `Invalid obligation));
  obligations_of_cmt "typed_reference_escape.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "return_alias" || obligation.name = "make_ref")
        && not (contains obligation.smt "result_state")
      then failwith "escaping reference content was not exposed";
      if
        obligation.name = "two_fresh_refs"
        && not (contains obligation.smt "distinct")
      then failwith "fresh escaping references lost identity separation";
      require `Valid obligation);
  obligations_of_cmt "typed_reference_escape_invalid.cmt"
  |> List.iter (require `Invalid);
  (match obligations_of_cmt "typed_reference_escape_missing_state.cmt" with
  | _ -> failwith "escaping reference without result_state was accepted"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_reference_escape_nested.cmt" with
  | _ -> failwith "nested escaping reference was accepted without ownership"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_physical_equality_invalid.cmt" with
  | _ -> failwith "physical equality on non-references was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_reachable_heap.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "read_pair"
        || obligation.name = "read_nested_box"
        || obligation.name = "read_some")
        && not (contains obligation.smt "call_reachable_state_")
      then failwith "reachable heap was not transferred at the call site";
      require `Valid obligation);
  obligations_of_cmt "typed_reachable_heap_invalid.cmt"
  |> List.iter (require `Invalid);
  (match obligations_of_cmt "typed_reachable_heap_incomplete.cmt" with
  | _ -> failwith "incomplete reachable-heap ownership was accepted"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_reachable_heap_recursive.cmt" with
  | _ -> failwith "recursive reachable heap was accepted without invariant"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_recursive_ownership.cmt"
  |> List.iter (fun obligation ->
      if
        (obligation.name = "read_new_link"
        || obligation.name = "borrowed_identity")
        && not (contains obligation.smt "call_reachable_state_")
      then failwith "recursive ownership frontier was not composed";
      if
        obligation.name = "head_nonnegative"
        && not (contains obligation.smt "region_value")
      then failwith "required region invariant was not added to the entry VC";
      require `Valid obligation);
  (match obligations_of_cmt "typed_recursive_ownership_bad_permission.cmt" with
  | _ -> failwith "unknown ownership permission was accepted"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_recursive_ownership_linear_invalid.cmt" with
  | _ -> failwith "ownership region was consumed twice"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_recursive_ownership_alias_invalid.cmt" with
  | _ -> failwith "borrowed ownership alias was consumed"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_recursive_ownership_bad_tail.cmt" with
  | _ -> failwith "unowned recursive tail was accepted as a region"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_conditional_resume.cmt"
  |> List.iter (fun obligation ->
      if obligation.name = "conditional" && not (contains obligation.smt "flag")
      then failwith "conditional continuation lost its branch guard";
      require `Valid obligation);
  (match obligations_of_cmt "typed_multishot_unsupported.cmt" with
  | _ -> failwith "sequential multi-shot continuation was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_recursive_bad_measure.cmt"
  |> List.iter (require `Invalid);
  (match obligations_of_cmt "typed_recursive_missing_measure.cmt" with
  | _ -> failwith "recursive function without a measure was accepted"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_recursive_missing_summary.cmt" with
  | _ -> failwith "recursive function without a summary was accepted"
  | exception Location.Error _ -> ());
  (match obligations_of_cmt "typed_recursive_coverage.cmt" with
  | _ -> failwith "safety summary was unsoundly reused for recursive coverage"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_unsupported.cmt" |> List.iter (require `Valid);
  obligations_of_cmt "typed_choice_incomplete.cmt"
  |> List.iter (fun obligation ->
      match (obligation.mode, solve obligation) with
      | Over, Valid -> ()
      | Under, Invalid model when contains model "missing_result" -> ()
      | _ -> failwith "choice upper/lower bounds were not distinguished");
  let run command = if Sys.command command <> 0 then failwith command in
  run "ocamlc -bin-annot -c ../examples/lemma_theory.mli -o lemma_theory.cmi";
  run
    "ocamlc -bin-annot -I . -c ../examples/lemma_theory.ml -o lemma_theory.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/lemma_client.ml -o lemma_client.cmo";
  write_rmi ~cmti:"lemma_theory.cmti" ~output:"lemma_theory.rmi";
  if not (Sys.file_exists "lemma_theory.rmi.rpa") then
    failwith "stable proof artifact sidecar was not emitted";
  if replay_proof "lemma_theory.rmi.rpa" <> 2 then
    failwith "proof replay returned the wrong lemma count";
  obligations_of_cmt_with_theories ~theories:[ "lemma_theory.rmi" ]
    "lemma_client.cmt"
  |> List.iter (fun obligation ->
      if obligation.trusted_axioms <> [ "Lemma_theory.p_implies_q" ] then
        failwith "checked lemma changed trusted axiom provenance";
      if
        obligation.checked_lemmas
        <> [
             "Lemma_theory.not_q_implies_not_p";
             "Lemma_theory.p_implies_q_checked";
           ]
      then failwith "checked lemma provenance was not imported";
      (match obligation.proof_artifacts with
      | [ first; second ] ->
          if first.lemma_name <> "Lemma_theory.not_q_implies_not_p" then
            failwith "verification artifact names the wrong lemma";
          if first.artifact_version <> 1 then
            failwith "verification artifact has the wrong format version";
          if String.length first.statement_digest <> 64 then
            failwith "verification artifact has no statement digest";
          if first.statement = "" then
            failwith "verification artifact has no canonical statement";
          if first.digest_algorithm <> "sha256" then
            failwith "verification artifact has the wrong digest algorithm";
          if String.length first.vc_digest <> 64 then
            failwith "verification artifact has no VC digest";
          if not (contains first.vc_smt "(check-sat)") then
            failwith "verification artifact does not contain its replay VC";
          if not (contains first.solver "Z3") then
            failwith "verification artifact has no solver identity";
          if first.timeout_seconds <> 10 then
            failwith "verification artifact has the wrong timeout";
          if first.trusted_axioms <> [ "Lemma_theory.p_implies_q" ] then
            failwith "verification artifact lost trusted dependencies";
          if first.checked_dependencies <> [] then
            failwith "first lemma invented checked dependencies";
          if
            second.checked_dependencies
            <> [ "Lemma_theory.not_q_implies_not_p" ]
          then failwith "lemma declaration order was not preserved"
      | _ -> failwith "checked lemma verification artifact was not imported");
      if not (contains obligation.smt "; checked lemma:") then
        failwith "checked lemma was not asserted in the client SMT theory";
      require `Valid obligation);
  let read_file path =
    let channel = open_in_bin path in
    Fun.protect
      ~finally:(fun () -> close_in channel)
      (fun () -> really_input_string channel (in_channel_length channel))
  in
  let write_file path contents =
    let channel = open_out_bin path in
    Fun.protect
      ~finally:(fun () -> close_out channel)
      (fun () -> output_string channel contents)
  in
  let replace_once text pattern replacement =
    let rec find index =
      if index + String.length pattern > String.length text then raise Not_found
      else if String.sub text index (String.length pattern) = pattern then index
      else find (index + 1)
    in
    let index = find 0 in
    String.sub text 0 index ^ replacement
    ^ String.sub text
        (index + String.length pattern)
        (String.length text - index - String.length pattern)
  in
  let tampered =
    replace_once (read_file "lemma_theory.rmi.rpa") "check-sat" "check-sax"
  in
  write_file "lemma_theory.tampered.rpa" tampered;
  (match replay_proof "lemma_theory.tampered.rpa" with
  | _ -> failwith "tampered proof artifact replayed successfully"
  | exception Location.Error _ -> ());
  write_file "lemma_theory_tampered.rmi" (read_file "lemma_theory.rmi");
  write_file "lemma_theory_tampered.rmi.rpa" tampered;
  (match
     obligations_of_cmt_with_theories
       ~theories:[ "lemma_theory_tampered.rmi" ]
       "lemma_client.cmt"
   with
  | _ -> failwith "client imported a tampered proof sidecar"
  | exception Location.Error _ -> ());
  run
    "ocamlc -bin-annot -c ../examples/invalid_lemma_theory.mli -o \
     invalid_lemma_theory.cmi";
  if Sys.file_exists "invalid_lemma_theory.rmi" then
    Sys.remove "invalid_lemma_theory.rmi";
  if Sys.file_exists "invalid_lemma_theory.rmi.rpa" then
    Sys.remove "invalid_lemma_theory.rmi.rpa";
  (match
     write_rmi ~cmti:"invalid_lemma_theory.cmti"
       ~output:"invalid_lemma_theory.rmi"
   with
  | () -> failwith "an invalid lemma was exported"
  | exception Location.Error _ ->
      if Sys.file_exists "invalid_lemma_theory.rmi" then
        failwith "failed lemma checking left an .rmi artifact";
      if Sys.file_exists "invalid_lemma_theory.rmi.rpa" then
        failwith "failed lemma checking left a proof sidecar");
  run
    "ocamlc -bin-annot -c ../examples/slicing_theory.mli -o slicing_theory.cmi";
  run
    "ocamlc -bin-annot -I . -c ../examples/slicing_theory.ml -o \
     slicing_theory.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/slicing_client.ml -o \
     slicing_client.cmo";
  write_rmi ~cmti:"slicing_theory.cmti" ~output:"slicing_theory.rmi";
  obligations_of_cmt_with_theories ~theories:[ "slicing_theory.rmi" ]
    "slicing_client.cmt"
  |> List.iter (fun obligation ->
      (match obligation.name with
      | "use_left" ->
          if
            obligation.trusted_axioms <> [ "Slicing_theory.p_implies_q" ]
            || obligation.checked_lemmas
               <> [ "Slicing_theory.not_q_implies_not_p" ]
          then failwith "left theory slice has the wrong provenance";
          if
            contains obligation.smt "r_implies_s"
            || contains obligation.smt "not_s_implies_not_r"
          then failwith "left theory slice retained the disjoint right cluster"
      | "use_right" ->
          if
            obligation.trusted_axioms <> [ "Slicing_theory.r_implies_s" ]
            || obligation.checked_lemmas
               <> [ "Slicing_theory.not_s_implies_not_r" ]
          then failwith "right theory slice has the wrong provenance";
          if
            contains obligation.smt "p_implies_q"
            || contains obligation.smt "not_q_implies_not_p"
          then failwith "right theory slice retained the disjoint left cluster"
      | "identity" ->
          if
            obligation.trusted_axioms <> []
            || obligation.checked_lemmas <> []
            || obligation.proof_artifacts <> []
          then failwith "theory-free obligation retained imported statements";
          if contains obligation.smt "L_Slicing_theory" then
            failwith "theory-free obligation retained logic declarations"
      | name -> failwith ("unexpected slicing obligation " ^ name));
      require `Valid obligation);
  run
    "ocamlc -bin-annot -c ../examples/abstract_theory.mli -o \
     abstract_theory.cmi";
  run
    "ocamlc -bin-annot -I . -c ../examples/abstract_theory.ml -o \
     abstract_theory.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/abstract_client.ml -o \
     abstract_client.cmo";
  write_rmi ~cmti:"abstract_theory.cmti" ~output:"abstract_theory.rmi";
  obligations_of_cmt_with_theories ~theories:[ "abstract_theory.rmi" ]
    "abstract_client.cmt"
  |> List.iter (fun obligation ->
      (match obligation.name with
      | "through_alias" ->
          if obligation.trusted_axioms <> [ "Abstract_theory.Core.holds_all" ]
          then failwith "nested alias did not retain its scoped axiom";
          if not (contains obligation.smt "L_logic_Abstract_theory_Core_holds")
          then
            failwith "local/exported alias chain did not resolve its predicate"
      | "reflexive" ->
          if obligation.trusted_axioms <> [ "Abstract_theory.equal_refl" ] then
            failwith "abstract sort equality selected the wrong theory slice"
      | name -> failwith ("unexpected abstract theory obligation " ^ name));
      if not (contains obligation.smt "T_Abstract_theory") then
        failwith "abstract type did not use its qualified uninterpreted sort";
      require `Valid obligation);
  run
    "ocamlc -bin-annot -c ../examples/functor_theory.mli -o functor_theory.cmi";
  run
    "ocamlc -bin-annot -I . -c ../examples/functor_theory.ml -o \
     functor_theory.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/functor_client.ml -o \
     functor_client.cmo";
  write_rmi ~cmti:"functor_theory.cmti" ~output:"functor_theory.rmi";
  obligations_of_cmt_with_theories ~theories:[ "functor_theory.rmi" ]
    "functor_client.cmt"
  |> List.iter (fun obligation ->
      (match obligation.name with
      | "first_mark" ->
          if
            not
              (List.mem "First.mark_enabled" obligation.trusted_axioms
              && List.mem "Functor_theory.Arg1.enabled"
                   obligation.trusted_axioms)
          then failwith "first functor application has the wrong axiom";
          if not (contains obligation.smt "Make_Functor_theory_Arg1") then
            failwith "first application lost its applicative sort identity"
      | "first_again_mark" ->
          if
            not
              (List.mem "First_again.mark_enabled" obligation.trusted_axioms
              && List.mem "Functor_theory.Arg1.enabled"
                   obligation.trusted_axioms)
          then failwith "repeated functor application has the wrong axiom";
          if not (contains obligation.smt "Make_Functor_theory_Arg1") then
            failwith "same functor argument did not reuse its sort identity"
      | "second_mark" ->
          if
            not
              (List.mem "Second.mark_enabled" obligation.trusted_axioms
              && List.mem "Functor_theory.Arg2.enabled"
                   obligation.trusted_axioms)
          then failwith "second functor application has the wrong axiom";
          if not (contains obligation.smt "Make_Functor_theory_Arg2") then
            failwith "different functor argument did not separate its sort"
      | "fresh1_mark" ->
          if obligation.trusted_axioms <> [ "Fresh1.mark_all" ] then
            failwith "first generative application has the wrong axiom";
          if not (contains obligation.smt "T_Fresh1_t") then
            failwith "first unit functor application was not generative"
      | "fresh2_mark" ->
          if obligation.trusted_axioms <> [ "Fresh2.mark_all" ] then
            failwith "second generative application has the wrong axiom";
          if not (contains obligation.smt "T_Fresh2_t") then
            failwith "second unit functor application reused a fresh sort"
      | name -> failwith ("unexpected functor obligation " ^ name));
      require `Valid obligation);
  run "ocamlc -bin-annot -c ../examples/list_theory.mli -o list_theory.cmi";
  run "ocamlc -bin-annot -I . -c ../examples/list_theory.ml -o list_theory.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/theory_client.ml -o \
     theory_client.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/theory_bool_client.ml -o \
     theory_bool_client.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/generic_client.ml -o \
     generic_client.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/generic_client_invalid.ml -o \
     generic_client_invalid.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/generic_client_missing.ml -o \
     generic_client_missing.cmo";
  run "ocamlc -bin-annot -I . -c ../examples/horn_client.ml -o horn_client.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/generic_chain.ml -o \
     generic_chain.cmo";
  run
    "ocamlc -bin-annot -I . -c ../examples/theory_private_client.ml -o \
     theory_private_client.cmo";
  write_rmi ~cmti:"list_theory.cmti" ~output:"list_theory.rmi";
  obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
    "theory_client.cmt"
  |> List.iter (fun obligation ->
      if obligation.trusted_axioms <> [ "List_theory.hd_mem" ] then
        failwith "exported axiom provenance was not preserved";
      if not (contains obligation.smt "T_list_Int") then
        failwith "polymorphic theory was not instantiated at int list";
      require `Valid obligation);
  obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
    "theory_bool_client.cmt"
  |> List.iter (fun obligation ->
      if not (contains obligation.smt "T_list_Bool") then
        failwith "polymorphic theory was not instantiated at bool list";
      require `Valid obligation);
  obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
    "generic_client.cmt"
  |> List.iter (fun obligation ->
      if
        not
          (List.exists
             (fun ghost -> contains ghost "complement.property=(fun")
             obligation.ghost_instantiations)
      then
        failwith "resolved generic call did not report its ghost instantiation";
      if not (contains obligation.smt "declare-fun F_List_theory_complement")
      then failwith "generic runtime summary was not emitted to SMT";
      require `Valid obligation);
  obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
    "generic_client_invalid.cmt"
  |> List.iter (require `Invalid);
  (match
     obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
       "generic_client_missing.cmt"
   with
  | _ -> failwith "generic call without an argument refinement was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
    "horn_client.cmt"
  |> List.iter (fun obligation ->
      if
        not
          (List.exists
             (fun ghost -> contains ghost "horn_identity.property=(fun")
             obligation.ghost_instantiations)
      then failwith "Horn solver did not report its inferred predicate";
      require `Valid obligation);
  obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
    "generic_chain.cmt"
  |> List.iter (fun obligation ->
      if List.length obligation.ghost_instantiations <> 2 then
        failwith
          "generic result refinement was not propagated to the second call";
      require `Valid obligation);
  run
    "ocamlc -bin-annot -c ../examples/bad_horn_theory.mli -o \
     bad_horn_theory.cmi";
  (match
     write_rmi ~cmti:"bad_horn_theory.cmti" ~output:"bad_horn_theory.rmi"
   with
  | () -> failwith "Horn generic under disjunction was exported"
  | exception Location.Error _ -> ());
  obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
    "theory_private_client.cmt"
  |> List.iter (require `Invalid);
  (match
     obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
       "typed_valid.cmt"
   with
  | _ -> failwith "an unimported refinement theory was accepted"
  | exception Location.Error _ -> ());
  run
    "ocamlc -bin-annot -c ../examples/list_theory_changed.mli -o \
     list_theory.cmi";
  run
    "ocamlc -bin-annot -I . -c ../examples/theory_client.ml -o \
     theory_client_stale.cmo";
  (match
     obligations_of_cmt_with_theories ~theories:[ "list_theory.rmi" ]
       "theory_client_stale.cmt"
   with
  | _ -> failwith "a stale .rmi was accepted against a changed .cmi"
  | exception Location.Error _ -> ());
  if
    Sys.command
      "ocamlc -bin-annot -c ../examples/ill_typed.ml -o ill_typed.cmo \
       2>/dev/null"
    = 0
  then failwith "ordinary OCaml type checking should reject ill_typed.ml";
  if Sys.file_exists "ill_typed.cmt" then
    match obligations_of_cmt "ill_typed.cmt" with
    | _ ->
        failwith "the refinement checker accepted a partial ill-typed Typedtree"
    | exception Location.Error _ -> ()

let () =
  Alcotest.run "refinedOCaml"
    [
      ( "core judgments",
        [
          Alcotest.test_case "compositional checking" `Quick
            test_compositional_judgment;
          Alcotest.test_case "proof SHA-256" `Quick test_sha256;
          Alcotest.test_case "Hindley evars" `Quick test_hindley_evars;
          Alcotest.test_case "higher-sorted application" `Quick
            test_higher_sorted_hindley_application;
          Alcotest.test_case "recursive Horn fixpoint" `Quick
            test_mutually_recursive_horn_fixpoint;
          Alcotest.test_case "relational outcomes" `Quick
            test_relational_outcomes;
        ] );
      ( "Typedtree integration",
        [
          Alcotest.test_case "full verification matrix" `Slow integration_suite;
        ] );
    ]
