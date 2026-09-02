(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/elrond/stream.ml. *)

type stream = SNil | SCons of int * stream
type stream_case = Stream_case of int * stream

let rec stream_length value =
  match value with SNil -> 0 | SCons (_, tail) -> 1 + stream_length tail

let[@refined.predicate] stream_bounded (value : stream) (bound : int) : bool =
  stream_length value <= bound

let[@refined.predicate] valid_stream_case (case : stream_case) : bool =
  match case with
  | Stream_case (bound, value) -> bound >= 0 && stream_bounded value bound

let[@refined.logic] stream_head (value : stream) : int =
  match value with SNil -> 0 | SCons (head, _) -> head

let[@refined.logic] stream_tail (value : stream) : stream =
  match value with SNil -> SNil | SCons (_, tail) -> tail

let[@refined.logic] case_bound (case : stream_case) : int =
  match case with Stream_case (bound, _) -> bound

let[@refined.logic] case_stream (case : stream_case) : stream =
  match case with Stream_case (_, value) -> value

[@@@refined.axiom
{
  name = "stream_bounded_nil";
  quantifiers = [ ("forall", "bound", "int") ];
  body = "implies (bound >= 0) (stream_bounded SNil bound)";
}]

[@@@refined.axiom
{
  name = "stream_bounded_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "stream");
      ("forall", "bound", "int");
    ];
  body =
    "implies (bound > 0 && stream_bounded tail (bound - 1)) (stream_bounded \
     (SCons (head, tail)) bound)";
}]

[@@@refined.axiom
{
  name = "stream_bounded_elim";
  quantifiers = [ ("forall", "value", "stream"); ("forall", "bound", "int") ];
  body =
    "implies (bound >= 0 && stream_bounded value bound) (value = SNil || \
     (bound > 0 && value = SCons (stream_head value, stream_tail value) && \
     stream_bounded (stream_tail value) (bound - 1)))";
}]

[@@@refined.axiom
{
  name = "valid_stream_case_intro";
  quantifiers = [ ("forall", "bound", "int"); ("forall", "value", "stream") ];
  body =
    "implies (bound >= 0 && stream_bounded value bound) (valid_stream_case \
     (Stream_case (bound, value)))";
}]

[@@@refined.axiom
{
  name = "valid_stream_case_elim";
  quantifiers = [ ("forall", "case", "stream_case") ];
  body =
    "implies (valid_stream_case case) (case = Stream_case (case_bound case, \
     case_stream case) && case_bound case >= 0 && stream_bounded (case_stream \
     case) (case_bound case))";
}]

let[@refined.choose] choose_stream (left : stream) (_right : stream) : stream =
  left

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> head:int -> tail:stream -> \
          {result:stream_case | valid_stream_case result}";
       witness_relation =
         "result = Stream_case (bound, case_stream result) && (case_stream \
          result = SNil || (bound > 0 && case_stream result = SCons (head, \
          tail) && stream_bounded tail (bound - 1)))";
     }] stream_port (bound : int) (head : int) (tail : stream) : stream_case =
  Stream_case (bound, choose_stream SNil (SCons (head, tail)))

let runtime_examples (_unit : unit) =
  let two = SCons (10, SCons (20, SNil)) in
  stream_bounded two 2 && not (stream_bounded two 1)
