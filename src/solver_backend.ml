open Refined_ir
open Refined_types

let timeout_seconds =
  match Sys.getenv_opt "REFINED_SOLVER_TIMEOUT_SECONDS" with
  | None -> 10
  | Some value -> (
      match int_of_string_opt value with
      | Some seconds when seconds > 0 -> seconds
      | _ ->
          invalid_arg
            "REFINED_SOLVER_TIMEOUT_SECONDS must be a positive integer")

let read_all channel =
  let buffer = Buffer.create 1024 in
  (try
     while true do
       Buffer.add_string buffer (input_line channel);
       Buffer.add_char buffer '\n'
     done
   with End_of_file -> ());
  Buffer.contents buffer

let solve obligation =
  let input, output, error =
    Unix.open_process_full
      (Printf.sprintf "z3 -in -T:%d" timeout_seconds)
      (Unix.environment ())
  in
  output_string output obligation.smt;
  close_out output;
  let stdout = read_all input in
  let stderr = read_all error in
  ignore (Unix.close_process_full (input, output, error));
  let first_line =
    match String.split_on_char '\n' stdout with
    | line :: _ -> String.trim line
    | [] -> ""
  in
  match first_line with
  | "unsat" -> Valid
  | "sat" -> Invalid stdout
  | "unknown" -> Unknown (stdout ^ stderr)
  | _ -> Unknown (stdout ^ stderr)

let solver_identity () =
  let channel = Unix.open_process_in "z3 -version" in
  let result =
    Fun.protect
      ~finally:(fun () -> ignore (Unix.close_process_in channel))
      (fun () ->
        match input_line channel with
        | line -> String.trim line
        | exception End_of_file -> "z3 (version unavailable)")
  in
  result
