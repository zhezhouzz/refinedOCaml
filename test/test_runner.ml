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

let () =
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
