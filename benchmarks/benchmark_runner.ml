open Refined_core

type positive_fixture = {
  source : string;
  output : string;
  obligations : string list;
  runtime : string;
}

let compile source output =
  let command =
    Printf.sprintf "ocamlc -bin-annot -c %s -o %s.cmo" (Filename.quote source)
      (Filename.quote output)
  in
  if Sys.command command <> 0 then failwith ("failed to compile " ^ source)

let check_result expected obligation =
  match (expected, solve obligation) with
  | `Valid, Valid -> ()
  | `Invalid, Invalid _ -> ()
  | `Valid, Invalid model ->
      failwith (Printf.sprintf "%s is invalid:\n%s" obligation.name model)
  | `Invalid, Valid ->
      failwith (Printf.sprintf "%s unexpectedly passed" obligation.name)
  | _, Unknown reason ->
      failwith (Printf.sprintf "%s is unknown:\n%s" obligation.name reason)

let verify_count source output expected =
  compile source output;
  let obligations = obligations_of_cmt (output ^ ".cmt") in
  if List.length obligations <> expected then
    failwith
      (Printf.sprintf "%s produced %d obligations; expected %d" source
         (List.length obligations) expected);
  List.iter (check_result `Valid) obligations

let verify_named source output expected_names expected_result =
  compile source output;
  let obligations = obligations_of_cmt (output ^ ".cmt") in
  let actual_names =
    List.map (fun obligation -> obligation.name) obligations
    |> List.sort compare
  in
  let expected_names = List.sort compare expected_names in
  if actual_names <> expected_names then
    failwith
      (Printf.sprintf "%s produced obligations [%s]; expected [%s]" source
         (String.concat ", " actual_names)
         (String.concat ", " expected_names));
  List.iter (check_result expected_result) obligations

let run_runtime fixture =
  let executable = fixture.output ^ "_runtime.exe" in
  let command =
    Printf.sprintf "ocamlc %s.cmo %s -o %s"
      (Filename.quote fixture.output)
      (Filename.quote fixture.runtime)
      (Filename.quote executable)
  in
  if Sys.command command <> 0 then
    failwith ("failed to link runtime examples for " ^ fixture.source);
  if Sys.command ("./" ^ executable) <> 0 then
    failwith ("runtime examples failed for " ^ fixture.source)

let contains text fragment =
  let text_length = String.length text in
  let fragment_length = String.length fragment in
  let rec search offset =
    if offset + fragment_length > text_length then false
    else if String.sub text offset fragment_length = fragment then true
    else search (offset + 1)
  in
  fragment_length = 0 || search 0

let read_file path =
  let channel = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let liquid_manifest =
  List.map
    (fun name -> ("src/" ^ name ^ ".lhs", "liquidhaskell/classics.ml"))
    [
      "02-logic";
      "03-basic";
      "04-poly";
      "05-datatypes";
      "06-measure-bool";
      "07-measure-int";
      "08-measure-sets";
      "10-case-study-associative-maps";
      "11-case-study-pointers";
    ]
  @ [
      ("src/09-case-study-lazy-queues.lhs", "liquidhaskell/lazy_queue.ml");
      ("src/12-case-study-AVL.lhs", "liquidhaskell/avl.ml");
    ]

let algorithm_coverage =
  [
    "data/PLDI23/basic/boundlist.ml";
    "data/PLDI23/basic/duplicate_list.ml";
    "data/PLDI23/elrond/LeftistHeap.ml";
    "data/PLDI23/stlc/gen_term_size.ml";
    "data/PLDI23/stlc/stlc.ml";
  ]

let coverage_manifest =
  [
    ("data/PLDI23/basic/boundlist.ml", "coveragetype/boundlist.ml");
    ("data/PLDI23/basic/duplicate_list.ml", "coveragetype/duplicate_list.ml");
    ("data/PLDI23/basic/sortedlist_simpl.ml", "coveragetype/semantic_lists.ml");
    ( "data/PLDI23/elrond/BankersQueue.ml",
      "coveragetype/semantic_bankers_queue.ml" );
    ( "data/PLDI23/elrond/BatchedQueue.ml",
      "coveragetype/semantic_batched_queue.ml" );
    ("data/PLDI23/elrond/LeftistHeap.ml", "coveragetype/leftist_heap.ml");
    ("data/PLDI23/elrond/UnbalanceSet.ml", "coveragetype/semantic_bst.ml");
    ("data/PLDI23/elrond/UniqueList.ml", "coveragetype/semantic_lists.ml");
    ("data/PLDI23/elrond/stream.ml", "coveragetype/semantic_stream.ml");
    ( "data/PLDI23/leonidas/CompleteTree.ml",
      "coveragetype/semantic_complete_tree.ml" );
    ("data/PLDI23/leonidas/SizedBST.ml", "coveragetype/semantic_bst.ml");
    ( "data/PLDI23/quickcheck/SizedHeap.ml",
      "coveragetype/semantic_sized_heap.ml" );
    ("data/PLDI23/quickcheck/SizedSet.ml", "coveragetype/semantic_bst.ml");
    ( "data/PLDI23/quickchick/RedBlackTree.ml",
      "coveragetype/semantic_red_black_tree.ml" );
    ("data/PLDI23/quickchick/SizedList.ml", "coveragetype/semantic_lists.ml");
    ( "data/PLDI23/quickchick/SizedTree.ml",
      "coveragetype/semantic_sized_tree.ml" );
    ("data/PLDI23/quickchick/SortedList.ml", "coveragetype/semantic_lists.ml");
    ("data/PLDI23/stlc/gen_term_size.ml", "coveragetype/semantic_stlc.ml");
    ("data/PLDI23/stlc/stlc.ml", "coveragetype/semantic_stlc.ml");
    ("data/monad/case1.ml", "coveragetype/semantic_monad_case1.ml");
    ( "data/monad/coverage_monad_library.ml",
      "coveragetype/semantic_monad_library.ml" );
    ("data/monad/herdtools7.ml", "coveragetype/semantic_herdtools.ml");
    ("data/monad/test.ml", "coveragetype/semantic_monad_return.ml");
    ("data/monad/tezos.ml", "coveragetype/semantic_tezos.ml");
    ("data/monad/tezos_test.ml", "coveragetype/semantic_tezos_test.ml");
    ("data/monad/tree2list.ml", "coveragetype/semantic_tree2list.ml");
    ("data/monad/vellvm.ml", "coveragetype/semantic_vellvm.ml");
    ("data/monad/xen_api.ml", "coveragetype/semantic_xen_api.ml");
    ("data/monad/zipperposition.ml", "coveragetype/semantic_zipperposition.ml");
  ]

let validate_semantic_fixture fixture =
  if not (Sys.file_exists fixture) then
    failwith ("missing benchmark fixture " ^ fixture);
  let contents = read_file fixture in
  if contains contents ": bool = false" then
    failwith ("constant-false predicate in semantic fixture " ^ fixture);
  if contains contents "(target :" then
    failwith ("target-seed adapter in semantic fixture " ^ fixture)

let validate_manifest () =
  let channel = open_in "manifest.tsv" in
  let lines =
    Fun.protect
      ~finally:(fun () -> close_in channel)
      (fun () -> In_channel.input_lines channel)
  in
  let rows =
    match lines with
    | header :: rows
      when header = "suite\trevision\tupstream_path\tlocal_fixture\tstatus" ->
        rows
    | _ -> failwith "benchmark manifest has an invalid header"
  in
  let seen_coverage = ref [] in
  let seen_liquid = ref [] in
  let liquid, coverage =
    List.fold_left
      (fun (liquid, coverage) row ->
        match String.split_on_char '\t' row with
        | [ suite; revision; upstream; fixture; status ] -> (
            let local_fixture =
              match String.starts_with ~prefix:"benchmarks/" fixture with
              | true -> String.sub fixture 11 (String.length fixture - 11)
              | false -> fixture
            in
            match suite with
            | "liquidhaskell"
              when revision = "f92259ca775f07b7285187ad27affd0e31e63093"
                   && status
                      =
                      if local_fixture = "liquidhaskell/classics.ml" then
                        "adapted-verified"
                      else "algorithm-verified" ->
                if
                  List.assoc_opt upstream liquid_manifest <> Some local_fixture
                  || List.mem upstream !seen_liquid
                then
                  failwith ("invalid or duplicate LiquidHaskell row " ^ upstream);
                seen_liquid := upstream :: !seen_liquid;
                if not (Sys.file_exists local_fixture) then
                  failwith ("missing benchmark fixture " ^ fixture);
                (liquid + 1, coverage)
            | "coveragetype"
              when revision = "c158b803c1c50ad61829e4ae079710f9d6cca52a"
                   && status
                      =
                      if List.mem upstream algorithm_coverage then
                        "algorithm-verified"
                      else "semantic-adapter" -> (
                match List.assoc_opt upstream coverage_manifest with
                | Some expected when expected = local_fixture ->
                    if List.mem upstream !seen_coverage then
                      failwith ("duplicate CoverageType row " ^ upstream);
                    seen_coverage := upstream :: !seen_coverage;
                    validate_semantic_fixture local_fixture;
                    (liquid, coverage + 1)
                | Some expected ->
                    failwith
                      (Printf.sprintf "%s uses %s; expected %s" upstream
                         local_fixture expected)
                | None -> failwith ("unexpected CoverageType row " ^ upstream))
            | _ -> failwith ("invalid benchmark manifest row: " ^ row))
        | _ -> failwith ("invalid benchmark manifest row: " ^ row))
      (0, 0) rows
  in
  if liquid <> 11 || coverage <> List.length coverage_manifest then
    failwith
      (Printf.sprintf "manifest has %d LiquidHaskell and %d CoverageType rows"
         liquid coverage);
  let expected_upstreams =
    List.map fst coverage_manifest |> List.sort compare
  in
  if List.sort compare !seen_coverage <> expected_upstreams then
    failwith
      "benchmark manifest does not contain the exact CoverageType inventory"

let positive_fixtures =
  [
    {
      source = "coveragetype/semantic_lists.ml";
      output = "semantic_lists";
      obligations =
        [
          "sortedlist_simpl";
          "unique_list_port";
          "sized_list_port";
          "sorted_list_port";
        ];
      runtime = "coveragetype/semantic_lists_runtime.ml";
    };
    {
      source = "coveragetype/boundlist.ml";
      output = "coveragetype_boundlist";
      obligations = [ "bound_list_gen" ];
      runtime = "coveragetype/boundlist_runtime.ml";
    };
    {
      source = "coveragetype/duplicate_list.ml";
      output = "coveragetype_duplicate_list";
      obligations = [ "duplicate_list_gen" ];
      runtime = "coveragetype/duplicate_list_runtime.ml";
    };
    {
      source = "coveragetype/semantic_bankers_queue.ml";
      output = "semantic_bankers_queue";
      obligations = [ "bankers_queue_port" ];
      runtime = "coveragetype/semantic_bankers_queue_runtime.ml";
    };
    {
      source = "coveragetype/semantic_batched_queue.ml";
      output = "semantic_batched_queue";
      obligations = [ "batched_queue_port" ];
      runtime = "coveragetype/semantic_batched_queue_runtime.ml";
    };
    {
      source = "coveragetype/leftist_heap.ml";
      output = "coveragetype_leftist_heap";
      obligations = [ "int_range_inc"; "generate" ];
      runtime = "coveragetype/leftist_heap_runtime.ml";
    };
    {
      source = "coveragetype/semantic_bst.ml";
      output = "semantic_bst";
      obligations =
        [ "unbalanced_set_port"; "sized_bst_port"; "sized_set_port" ];
      runtime = "coveragetype/semantic_bst_runtime.ml";
    };
    {
      source = "coveragetype/semantic_stream.ml";
      output = "semantic_stream";
      obligations = [ "stream_port" ];
      runtime = "coveragetype/semantic_stream_runtime.ml";
    };
    {
      source = "coveragetype/semantic_complete_tree.ml";
      output = "semantic_complete_tree";
      obligations = [ "complete_tree_port" ];
      runtime = "coveragetype/semantic_complete_tree_runtime.ml";
    };
    {
      source = "coveragetype/semantic_sized_heap.ml";
      output = "semantic_sized_heap";
      obligations = [ "sized_heap_port" ];
      runtime = "coveragetype/semantic_sized_heap_runtime.ml";
    };
    {
      source = "coveragetype/semantic_red_black_tree.ml";
      output = "semantic_red_black_tree";
      obligations = [ "red_black_tree_port" ];
      runtime = "coveragetype/semantic_red_black_tree_runtime.ml";
    };
    {
      source = "coveragetype/semantic_sized_tree.ml";
      output = "semantic_sized_tree";
      obligations = [ "sized_tree_port" ];
      runtime = "coveragetype/semantic_sized_tree_runtime.ml";
    };
    {
      source = "coveragetype/semantic_stlc.ml";
      output = "semantic_stlc";
      obligations =
        [
          "int_range_inex";
          "vars_with_type";
          "gen_term_no_app";
          "gen_term_size_port";
          "stlc_port";
        ];
      runtime = "coveragetype/semantic_stlc_runtime.ml";
    };
    {
      source = "coveragetype/semantic_monad_case1.ml";
      output = "semantic_monad_case1";
      obligations = [ "monad_case1" ];
      runtime = "coveragetype/semantic_monad_case1_runtime.ml";
    };
    {
      source = "coveragetype/semantic_monad_library.ml";
      output = "semantic_monad_library";
      obligations = [ "coverage_monad_library" ];
      runtime = "coveragetype/semantic_monad_library_runtime.ml";
    };
    {
      source = "coveragetype/semantic_herdtools.ml";
      output = "semantic_herdtools";
      obligations = [ "herdtools7" ];
      runtime = "coveragetype/semantic_herdtools_runtime.ml";
    };
    {
      source = "coveragetype/semantic_monad_return.ml";
      output = "semantic_monad_return";
      obligations = [ "monad_test" ];
      runtime = "coveragetype/semantic_monad_return_runtime.ml";
    };
    {
      source = "coveragetype/semantic_tezos.ml";
      output = "semantic_tezos";
      obligations = [ "tezos" ];
      runtime = "coveragetype/semantic_tezos_runtime.ml";
    };
    {
      source = "coveragetype/semantic_tezos_test.ml";
      output = "semantic_tezos_test";
      obligations = [ "tezos_test" ];
      runtime = "coveragetype/semantic_tezos_test_runtime.ml";
    };
    {
      source = "coveragetype/semantic_tree2list.ml";
      output = "semantic_tree2list";
      obligations = [ "tree2list" ];
      runtime = "coveragetype/semantic_tree2list_runtime.ml";
    };
    {
      source = "coveragetype/semantic_vellvm.ml";
      output = "semantic_vellvm";
      obligations = [ "vellvm" ];
      runtime = "coveragetype/semantic_vellvm_runtime.ml";
    };
    {
      source = "coveragetype/semantic_xen_api.ml";
      output = "semantic_xen_api";
      obligations = [ "xen_api" ];
      runtime = "coveragetype/semantic_xen_api_runtime.ml";
    };
    {
      source = "coveragetype/semantic_zipperposition.ml";
      output = "semantic_zipperposition";
      obligations = [ "zipperposition" ];
      runtime = "coveragetype/semantic_zipperposition_runtime.ml";
    };
  ]

let liquid_algorithms =
  [
    {
      source = "liquidhaskell/lazy_queue.ml";
      output = "liquid_lazy_queue";
      obligations =
        [
          "rotate"; "makeq"; "empty"; "insert"; "remove"; "replicate"; "example";
        ];
      runtime = "liquidhaskell/lazy_queue_runtime.ml";
    };
    {
      source = "liquidhaskell/avl.ml";
      output = "liquid_avl";
      obligations = [ "node"; "balance"; "insert" ];
      runtime = "liquidhaskell/avl_runtime.ml";
    };
  ]

(* Mutate the verified algorithm itself and replay its concrete examples.
   These are runtime counterexamples, separate from SMT-invalid controls:
   quantified recursive theories can make Z3 return Unknown on false goals. *)
let runtime_mutations =
  [
    ( "heap_rank",
      "coveragetype/leftist_heap.ml",
      "Node (right_depth + 1, int_gen (), left, right)",
      "Node (right_depth + 2, int_gen (), left, right)" );
    ( "heap_depth",
      "coveragetype/leftist_heap.ml",
      "let left_depth = expected - 1 in",
      "let left_depth = 0 in" );
    ( "queue_rotation",
      "liquidhaskell/lazy_queue.ml",
      "else Q (rotate (length front) front back Nil, Nil)",
      "else Q (front, back)" );
    ( "queue_remove",
      "liquidhaskell/lazy_queue.ml",
      "Removed (head, makeq tail back)",
      "Removed (head, makeq tail Nil)" );
    ( "avl_height",
      "liquidhaskell/avl.ml",
      "Node (key, 1 + maximum (height left) (height right), left, right)",
      "Node (key, 2 + maximum (height left) (height right), left, right)" );
    ( "avl_rotation",
      "liquidhaskell/avl.ml",
      "node lower upper lk ll (node lk upper key lr right)",
      "node lower upper key left right" );
    ( "stlc_application",
      "coveragetype/semantic_stlc.ml",
      "in App (argument_type, function_term, argument_term)",
      "in Const 0" );
    ( "stlc_abstraction",
      "coveragetype/semantic_stlc.ml",
      "Abs (argument_type, gen_term_no_app (arrow_count result_type) (Bind \
       (argument_type, context)) result_type)",
      "Const 0" );
  ]

let write_file path contents =
  let channel = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel contents)

let run_runtime_mutation (name, source, before, after) =
  let contents = read_file source in
  let compact text =
    let buffer = Buffer.create (String.length text) in
    let indices = ref [] in
    String.iteri
      (fun index character ->
        if not (List.mem character [ ' '; '\n'; '\r'; '\t' ]) then (
          Buffer.add_char buffer character;
          indices := index :: !indices))
      text;
    (Buffer.contents buffer, Array.of_list (List.rev !indices))
  in
  let normalized, indices = compact contents in
  let before, _ = compact before in
  let offsets =
    List.init
      (max 0 (String.length normalized - String.length before + 1))
      Fun.id
    |> List.filter (fun index ->
        String.sub normalized index (String.length before) = before)
  in
  let offset =
    match offsets with
    | [ offset ] -> offset
    | _ -> failwith ("mutation must match exactly once: " ^ name)
  in
  let start = indices.(offset) in
  let stop = indices.(offset + String.length before - 1) + 1 in
  let mutated =
    String.sub contents 0 start
    ^ after
    ^ String.sub contents stop (String.length contents - stop)
  in
  let output = "mutation_" ^ name in
  write_file (output ^ ".ml") mutated;
  compile (output ^ ".ml") output;
  let checker = output ^ "_check.ml" in
  write_file checker
    (Printf.sprintf "let () = if not (%s.runtime_examples ()) then exit 1\n"
       (String.capitalize_ascii output));
  let executable = output ^ ".exe" in
  let link =
    Printf.sprintf "ocamlc -w -a %s.cmo %s -o %s" (Filename.quote output)
      (Filename.quote checker)
      (Filename.quote executable)
  in
  if Sys.command link <> 0 then failwith ("failed to link mutation " ^ name);
  if Sys.command ("./" ^ Filename.quote executable ^ " >/dev/null 2>&1") = 0
  then failwith ("runtime examples missed algorithm mutation " ^ name)

let negative_fixtures =
  [
    ( "coveragetype/basic_lists_bad.ml",
      "basic_lists_bad",
      [ "bound_list_below_floor"; "duplicate_list_wrong_item" ] );
    ( "coveragetype/leftist_heap_bad.ml",
      "leftist_heap_bad",
      [ "generate_bad_rank" ] );
    ( "coveragetype/semantic_sequences_bad.ml",
      "semantic_sequences_bad",
      [ "list_constructor_mutation"; "stream_constructor_mutation" ] );
    ( "coveragetype/semantic_queues_bad.ml",
      "semantic_queues_bad",
      [ "queue_nonempty_branch_mutation" ] );
    ( "coveragetype/semantic_trees_bad.ml",
      "semantic_trees_bad",
      [ "tree_node_branch_mutation" ] );
    ( "coveragetype/semantic_stlc_bad.ml",
      "semantic_stlc_bad",
      [ "stlc_application_mutation" ] );
    ( "coveragetype/semantic_monads_bad.ml",
      "semantic_monads_bad",
      [
        "monad_union_branch_mutation";
        "monad_return_relation_mutation";
        "monad_recursive_constructor_mutation";
      ] );
  ]

let () =
  try
    validate_manifest ();
    let positive_count =
      List.fold_left
        (fun count fixture -> count + List.length fixture.obligations)
        0 positive_fixtures
    in
    if positive_count <> 33 then
      failwith
        (Printf.sprintf "runner has %d CoverageType obligations; expected 33"
           positive_count);
    verify_count "liquidhaskell/classics.ml" "liquidhaskell_classics" 9;
    List.iter
      (fun fixture ->
        verify_named fixture.source fixture.output fixture.obligations `Valid;
        run_runtime fixture)
      liquid_algorithms;
    List.iter
      (fun fixture ->
        verify_named fixture.source fixture.output fixture.obligations `Valid;
        run_runtime fixture)
      positive_fixtures;
    List.iter
      (fun (source, output, obligations) ->
        verify_named source output obligations `Invalid)
      negative_fixtures;
    List.iter run_runtime_mutation runtime_mutations
  with exception_ ->
    Location.report_exception Format.err_formatter exception_;
    raise exception_
