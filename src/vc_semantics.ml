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
  assumptions : string list;
  side_conditions : string list;
  argument_witnesses : (string * string) list;
}

let declare buffer (name, sort) =
  Buffer.add_string buffer (Printf.sprintf "(declare-const %s %s)\n" name sort)

module type S = sig
  val mode : mode
  val encode : context -> unit
end

module Safety : S = struct
  let mode = Over

  let encode context =
    List.iter (declare context.buffer) context.arguments;
    List.iter (declare context.buffer) context.choices;
    let actual = Refinement_domain.Smt.equality "result" context.body in
    let judgment =
      Typing_judgment.Safety.synthesize ~rule:Function_body ~predicate:actual
        ~children:[]
    in
    let checked =
      Typing_judgment.Safety.check
        ~assumptions:(context.pre :: context.assumptions)
        ~expected:context.post judgment
    in
    let contract_obligation = Typing_judgment.Safety.obligation checked in
    let side_obligation =
      Refinement_domain.Smt.implies context.pre
        (Refinement_domain.Smt.conjunction context.side_conditions)
    in
    let obligation =
      if context.side_conditions = [] then contract_obligation
      else
        Refinement_domain.Smt.conjunction
          [ side_obligation; contract_obligation ]
    in
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert (not (let ((result %s)) %s)))\n" context.body
         obligation)
end

module Coverage : S = struct
  let mode = Under

  let encode context =
    let missing = "missing_result" in
    let body =
      Refinement_domain.Smt.conjunction
        (context.pre
        :: Refinement_domain.Smt.equality missing context.body
        :: context.assumptions)
    in
    let actual =
      match context.argument_witnesses with
      | [] ->
          Refinement_domain.Smt.exists
            (context.arguments @ context.choices)
            body
      | bindings ->
          let bindings =
            "("
            ^ String.concat " "
                (List.map
                   (fun (name, term) -> Printf.sprintf "(%s %s)" name term)
                   bindings)
            ^ ")"
          in
          Refinement_domain.Smt.exists context.choices
            (Printf.sprintf "(let %s %s)" bindings body)
    in
    let judgment =
      Typing_judgment.Coverage.synthesize ~rule:Function_body ~predicate:actual
        ~children:[]
    in
    let checked =
      Typing_judgment.Coverage.check ~assumptions:[] ~expected:context.post
        judgment
    in
    let contract_obligation = Typing_judgment.Coverage.obligation checked in
    let side_obligation =
      Refinement_domain.Smt.implies context.pre
        (Refinement_domain.Smt.conjunction context.side_conditions)
    in
    let obligation =
      if context.side_conditions = [] then contract_obligation
      else
        Refinement_domain.Smt.conjunction
          [ side_obligation; contract_obligation ]
    in
    if context.side_conditions <> [] then (
      List.iter (declare context.buffer) context.arguments;
      List.iter (declare context.buffer) context.choices);
    Buffer.add_string context.buffer
      (Printf.sprintf "(declare-const %s %s)\n" missing context.result_sort);
    Buffer.add_string context.buffer
      (Printf.sprintf "(assert (not %s))\n" obligation)
end

let semantics = function
  | Over -> (module Safety : S)
  | Under -> (module Coverage : S)

let encode mode context =
  let module Semantics = (val semantics mode : S) in
  if Semantics.mode <> mode then assert false;
  Semantics.encode context
