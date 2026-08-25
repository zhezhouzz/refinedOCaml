open Refined_ir
open Refined_types

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
    Unix.open_process_full "z3 -in -T:10" (Unix.environment ())
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
