open Refined_core

let require_valid obligation =
  match solve obligation with
  | Valid -> ()
  | Invalid model ->
      failwith (Printf.sprintf "%s is invalid:\n%s" obligation.name model)
  | Unknown reason ->
      failwith (Printf.sprintf "%s is unknown:\n%s" obligation.name reason)

let compile source output =
  let command =
    Printf.sprintf "ocamlc -bin-annot -c %s -o %s.cmo" (Filename.quote source)
      (Filename.quote output)
  in
  if Sys.command command <> 0 then failwith ("failed to compile " ^ source)

let verify source output expected =
  compile source output;
  let obligations = obligations_of_cmt (output ^ ".cmt") in
  if List.length obligations <> expected then
    failwith
      (Printf.sprintf "%s produced %d obligations; expected %d" source
         (List.length obligations) expected);
  List.iter require_valid obligations

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
  let liquid, coverage =
    List.fold_left
      (fun (liquid, coverage) row ->
        match String.split_on_char '\t' row with
        | [ suite; revision; upstream; fixture; "adapted-verified" ] -> (
            let local_fixture =
              match String.starts_with ~prefix:"benchmarks/" fixture with
              | true -> String.sub fixture 11 (String.length fixture - 11)
              | false -> fixture
            in
            if not (Sys.file_exists local_fixture) then
              failwith ("missing benchmark fixture " ^ fixture);
            match suite with
            | "liquidhaskell"
              when revision = "f92259ca775f07b7285187ad27affd0e31e63093"
                   && String.starts_with ~prefix:"src/" upstream ->
                (liquid + 1, coverage)
            | "coveragetype"
              when revision = "c158b803c1c50ad61829e4ae079710f9d6cca52a"
                   && String.starts_with ~prefix:"data/" upstream ->
                (liquid, coverage + 1)
            | _ -> failwith ("invalid benchmark manifest row: " ^ row))
        | _ -> failwith ("invalid benchmark manifest row: " ^ row))
      (0, 0) rows
  in
  if liquid <> 11 || coverage <> 29 then
    failwith
      (Printf.sprintf "manifest has %d LiquidHaskell and %d CoverageType rows"
         liquid coverage)

let () =
  try
    validate_manifest ();
    verify "liquidhaskell/classics.ml" "liquidhaskell_classics" 11;
    verify "coveragetype/adapted.ml" "coveragetype_adapted" 29
  with exception_ ->
    Location.report_exception Format.err_formatter exception_;
    raise exception_
