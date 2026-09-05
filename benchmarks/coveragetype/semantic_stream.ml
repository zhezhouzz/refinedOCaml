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
  name = "stream_bounded_elim";
  quantifiers = [ ("forall", "value", "stream"); ("forall", "bound", "int") ];
  body =
    "implies (bound >= 0 && stream_bounded value bound) (value = SNil || \
     (bound > 0 && value = SCons (stream_head value, stream_tail value) && \
     stream_bounded (stream_tail value) (bound - 1)))";
}]

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> {r:stream | stream_bounded r bound}";
       universals = [ "bound" ];
     }]
   [@refined.measure "bound"] rec stream_port (bound : int) : stream =
  if bound = 0 then SNil
  else if bool_gen () then SNil
  else
    let tail = stream_port (bound - 1) in
    SCons (int_gen (), tail)

let runtime_examples (_unit : unit) = stream_bounded (stream_port 3) 3
