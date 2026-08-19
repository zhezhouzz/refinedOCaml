open Refined_core

let files = ref []
let emit_dir = ref None

let add_file file = files := file :: !files

let options =
  [ ( "--emit-smt",
      Arg.String (fun path -> emit_dir := Some path),
      "DIR write every generated SMT-LIB obligation to DIR" ) ]

let write_smt dir obligation =
  let mode = mode_name obligation.mode in
  let path = Filename.concat dir (obligation.name ^ "." ^ mode ^ ".smt2") in
  let channel = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel obligation.smt)

let report obligation verdict =
  let pos = obligation.location.loc_start in
  let prefix =
    Printf.sprintf "%s:%d:%d: %s %s" pos.pos_fname pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1)
      (mode_name obligation.mode) obligation.name
  in
  match verdict with
  | Valid -> Printf.printf "%s: valid\n%!" prefix
  | Invalid model ->
      Printf.printf "%s: INVALID\n%s\n%!" prefix model
  | Unknown reason -> Printf.printf "%s: unknown\n%s\n%!" prefix reason

let () =
  Arg.parse options add_file
    "refined-ocaml [--emit-smt DIR] FILE.ml ...\n\nChecks [@refined.over] and [@refined.under] contracts.";
  if !files = [] then (Arg.usage options "refined-ocaml FILE.ml ..."; exit 2);
  Option.iter
    (fun dir -> if not (Sys.file_exists dir) then Unix.mkdir dir 0o755)
    !emit_dir;
  let failures = ref 0 in
  List.rev !files
  |> List.iter (fun file ->
         try
           obligations_of_file file
           |> List.iter (fun obligation ->
                  Option.iter (fun dir -> write_smt dir obligation) !emit_dir;
                  let verdict = solve obligation in
                  report obligation verdict;
                  match verdict with Valid -> () | Invalid _ | Unknown _ -> incr failures)
         with
         | Location.Error error ->
             Location.print_report Format.err_formatter error;
             incr failures
         | Sys_error message ->
             prerr_endline message;
             incr failures);
  if !failures <> 0 then exit 1
