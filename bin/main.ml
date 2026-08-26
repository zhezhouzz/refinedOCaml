open Refined_core

let files = ref []
let emit_dir = ref None
let theories = ref []
let rmi_output = ref None
let add_file file = files := file :: !files

let options =
  [
    ( "--emit-smt",
      Arg.String (fun path -> emit_dir := Some path),
      "DIR write every generated SMT-LIB obligation to DIR" );
    ( "--theory",
      Arg.String (fun path -> theories := path :: !theories),
      "FILE.rmi import a separately compiled refinement theory" );
    ( "--emit-rmi",
      Arg.String (fun path -> rmi_output := Some path),
      "FILE write the theory exported by one input .cmti and exit" );
  ]

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
  if obligation.ghost_instantiations <> [] then
    Printf.printf "  ghost instantiations: %s\n%!"
      (String.concat ", " obligation.ghost_instantiations)

let () =
  Arg.parse options add_file
    "refined-ocaml [--theory FILE.rmi] [--emit-smt DIR] FILE.cmt ...\n\n\
     Checks [@refined.over] and [@refined.coverage] contracts after OCaml \
     typing.";
  if !files = [] then (
    Arg.usage options "refined-ocaml FILE.cmt ...";
    exit 2);
  (match !rmi_output with
  | Some output -> (
      match List.rev !files with
      | [ cmti ] ->
          write_rmi ~cmti ~output;
          Printf.printf "%s: wrote refinement interface %s\n%!" cmti output;
          exit 0
      | _ ->
          prerr_endline "--emit-rmi requires exactly one .cmti input";
          exit 2)
  | None -> ());
  List.iter
    (fun file ->
      if not (Filename.check_suffix file ".cmt") then (
        Printf.eprintf
          "%s: expected a typed .cmt implementation; compile the .ml file with \
           -bin-annot first\n\
           %!"
          file;
        exit 2))
    !files;
  Option.iter
    (fun dir -> if not (Sys.file_exists dir) then Unix.mkdir dir 0o755)
    !emit_dir;
  let failures = ref 0 in
  List.rev !files
  |> List.iter (fun file ->
      try
        obligations_of_cmt_with_theories ~theories:(List.rev !theories) file
        |> List.iter (fun obligation ->
            Option.iter (fun dir -> write_smt dir obligation) !emit_dir;
            let verdict = solve obligation in
            report obligation verdict;
            match verdict with
            | Valid -> ()
            | Invalid _ | Unknown _ -> incr failures)
      with
      | Location.Error error ->
          Location.print_report Format.err_formatter error;
          incr failures
      | Sys_error message ->
          prerr_endline message;
          incr failures);
  if !failures <> 0 then exit 1
