open Refined_types

type declaration = string * string

type context = {
  buffer : Buffer.t;
  arguments : declaration list;
  choices : declaration list;
  result_sort : string;
  body : string;
  pre : string;
  post : string;
}

let declare buffer (name, sort) =
  Buffer.add_string buffer (Printf.sprintf "(declare-const %s %s)\n" name sort)

let binder (name, sort) = Printf.sprintf "(%s %s)" name sort

module type S = sig
  val mode : mode
  val encode : context -> unit
end

module Safety : S = struct
  let mode = Over

  let encode context =
    List.iter (declare context.buffer) context.arguments;
    List.iter (declare context.buffer) context.choices;
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert %s)\n" context.pre);
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert (not (let ((result %s)) %s)))\n" context.body
         context.post)
end

module Coverage : S = struct
  let mode = Under

  let encode context =
    let missing = "missing_result" in
    let quantified =
      "("
      ^ String.concat " "
          (List.map binder context.arguments @ List.map binder context.choices)
      ^ ")"
    in
    Buffer.add_string context.buffer
      (Printf.sprintf "(declare-const %s %s)\n" missing context.result_sort);
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert %s)\n" context.post);
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert (forall %s (not (and %s (= %s %s)))))\n"
         quantified context.pre missing context.body)
end

let semantics = function
  | Over -> (module Safety : S)
  | Under -> (module Coverage : S)

let encode mode context =
  let module Semantics = (val semantics mode : S) in
  if Semantics.mode <> mode then assert false;
  Semantics.encode context
