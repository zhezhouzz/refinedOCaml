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
      failwith (obligation.name ^ " should be valid")
  | `Invalid, (Valid | Unknown _) ->
      failwith (obligation.name ^ " should be invalid")

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

let () =
  test_compositional_judgment ();
  test_hindley_evars ();
  test_higher_sorted_hindley_application ();
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
  (match obligations_of_cmt "typed_unsupported.cmt" with
  | _ -> failwith "an unsupported effectful Typedtree was accepted"
  | exception Location.Error _ -> ());
  obligations_of_cmt "typed_choice_incomplete.cmt"
  |> List.iter (fun obligation ->
      match (obligation.mode, solve obligation) with
      | Over, Valid -> ()
      | Under, Invalid model when contains model "missing_result" -> ()
      | _ -> failwith "choice upper/lower bounds were not distinguished");
  let run command = if Sys.command command <> 0 then failwith command in
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
