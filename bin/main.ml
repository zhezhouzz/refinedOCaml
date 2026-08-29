open Refined_core
open Cmdliner

let write_smt dir obligation =
  let mode = mode_name obligation.mode in
  let path = Filename.concat dir (obligation.name ^ "." ^ mode ^ ".smt2") in
  let channel = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel obligation.smt)

let report obligation verdict =
  let pos = obligation.location.Source_span.start in
  let prefix =
    Printf.sprintf "%s:%d:%d: %s %s" obligation.location.file pos.line
      (pos.column + 1)
      (mode_name obligation.mode)
      obligation.name
  in
  (match verdict with
  | Valid -> Printf.printf "%s: valid\n%!" prefix
  | Invalid model -> Printf.printf "%s: INVALID\n%s\n%!" prefix model
  | Unknown reason -> Printf.printf "%s: unknown\n%s\n%!" prefix reason);
  if obligation.trusted_axioms <> [] then
    Printf.printf "  trusted axioms: %s\n%!"
      (String.concat ", " obligation.trusted_axioms);
  if obligation.checked_lemmas <> [] then
    Printf.printf "  checked lemmas: %s\n%!"
      (String.concat ", " obligation.checked_lemmas);
  if obligation.proof_artifacts <> [] then
    Printf.printf "  verification artifacts: %s\n%!"
      (String.concat ", "
         (List.map
            (fun artifact ->
              Printf.sprintf "%s@%s" artifact.lemma_name artifact.vc_digest)
            obligation.proof_artifacts));
  if obligation.ghost_instantiations <> [] then
    Printf.printf "  ghost instantiations: %s\n%!"
      (String.concat ", " obligation.ghost_instantiations)

let location_error error =
  Format.asprintf "%a" Location.print_report error |> String.trim

let check_action theories emit_dir files =
  if files = [] then Error "at least one .cmt input is required"
  else
    match
      List.find_opt (fun file -> not (Filename.check_suffix file ".cmt")) files
    with
    | Some file ->
        Error
          (Printf.sprintf
             "%s: expected a typed .cmt implementation; compile with \
              -bin-annot first"
             file)
    | None -> (
        try
          Option.iter
            (fun dir -> if not (Sys.file_exists dir) then Unix.mkdir dir 0o755)
            emit_dir;
          let failures = ref 0 in
          List.iter
            (fun file ->
              try
                obligations_of_cmt_with_theories ~theories file
                |> List.iter (fun obligation ->
                    Option.iter (fun dir -> write_smt dir obligation) emit_dir;
                    let verdict = solve obligation in
                    report obligation verdict;
                    match verdict with
                    | Valid -> ()
                    | Invalid _ | Unknown _ -> incr failures)
              with
              | Location.Error error ->
                  Format.eprintf "%a@." Location.print_report error;
                  incr failures
              | Sys_error message ->
                  prerr_endline message;
                  incr failures)
            files;
          if !failures = 0 then Ok ()
          else
            Error (Printf.sprintf "%d verification input(s) failed" !failures)
        with Sys_error message -> Error message)

let emit_rmi_action output cmti =
  try
    write_rmi ~cmti ~output;
    Printf.printf "%s: wrote refinement interface %s and proof bundle %s\n%!"
      cmti output (output ^ ".rpa");
    Ok ()
  with
  | Location.Error error -> Error (location_error error)
  | Sys_error message -> Error message

let replay_action path =
  try
    let count = replay_proof path in
    Printf.printf "%s: replayed %d proof artifact(s)\n%!" path count;
    Ok ()
  with
  | Location.Error error -> Error (location_error error)
  | Sys_error message -> Error message

let cmd_result = function
  | Ok () -> `Ok ()
  | Error message -> `Error (false, message)

let theories =
  let doc = "Import a separately compiled refinement theory $(docv)." in
  Arg.(value & opt_all file [] & info [ "theory" ] ~docv:"FILE.rmi" ~doc)

let emit_dir =
  let doc = "Write every generated SMT-LIB obligation to $(docv)." in
  Arg.(value & opt (some string) None & info [ "emit-smt" ] ~docv:"DIR" ~doc)

let cmt_files = Arg.(value & pos_all file [] & info [] ~docv:"FILE.cmt")

let output =
  let doc = "Write the refinement theory cache to $(docv)." in
  Arg.(
    required
    & opt (some string) None
    & info [ "o"; "output" ] ~docv:"FILE.rmi" ~doc)

let cmti = Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE.cmti")
let proof = Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE.rpa")

let check_cmd =
  let doc = "check refinement contracts in typed OCaml implementations" in
  let term =
    Term.(
      ret
        (const (fun t e f -> cmd_result (check_action t e f))
        $ theories $ emit_dir $ cmt_files))
  in
  Cmd.v (Cmd.info "check" ~doc) term

let emit_rmi_cmd =
  let doc = "export a separately compiled refinement theory" in
  let term =
    Term.(
      ret
        (const (fun output cmti -> cmd_result (emit_rmi_action output cmti))
        $ output $ cmti))
  in
  Cmd.v (Cmd.info "emit-rmi" ~doc) term

let replay_cmd =
  let doc = "validate and re-solve a stable proof artifact bundle" in
  let term =
    Term.(ret (const (fun path -> cmd_result (replay_action path)) $ proof))
  in
  Cmd.v (Cmd.info "replay" ~doc) term

let main =
  let doc = "bidirectional refinement checking for typed OCaml" in
  let info = Cmd.info "refined-ocaml" ~version:"dev" ~doc in
  Cmd.group info [ check_cmd; emit_rmi_cmd; replay_cmd ]

let () = exit (Cmd.eval main)
