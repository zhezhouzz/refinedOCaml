(* SPDX-License-Identifier: MIT
   Recursive port; finite streams use strict spines. Bankers cached lengths are retained. *)
type seq = Nil | Cons of int * seq
type queue = Queue of seq * seq

let[@refined.logic] rec length (s : seq) : int =
  match s with Nil -> 0 | Cons (_, t) -> 1 + length t

let[@refined.logic] head (s : seq) : int =
  match s with Nil -> 0 | Cons (h, _) -> h

let[@refined.logic] tail (s : seq) : seq =
  match s with Nil -> Nil | Cons (_, t) -> t

[@@@refined.axiom
{
  name = "length_elim";
  quantifiers = [ ("forall", "s", "seq") ];
  body =
    "(s = Nil && length s = 0) || (s = Cons (head s, tail s) && length s > 0 \
     && length (tail s) = length s - 1)";
}]

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.coverage
     {
       type_ =
         "lower:int -> upper:{upper:int | lower <= upper} -> {r:int | lower <= \
          r && r <= upper}";
       universals = [ "lower"; "upper" ];
       witness_relation = "true";
     }] int_range_inc (lower : int) (upper : int) : int =
  let x = int_gen () in
  if x < lower then lower else if x > upper then upper else x

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {r:seq | length r = size}";
       universals = [ "size" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec seq_gen (size : int) : seq =
  if size = 0 then Nil else Cons (int_gen (), seq_gen (size - 1))

let[@refined.predicate] target (q : queue) (size : int) : bool =
  match q with Queue (f, r) -> length f = size && length r < size

let[@refined.logic] front (q : queue) : seq = match q with Queue (f, _) -> f
let[@refined.logic] rear (q : queue) : seq = match q with Queue (_, r) -> r

[@@@refined.axiom
{
  name = "queue_elim";
  quantifiers = [ ("forall", "q", "queue"); ("forall", "size", "int") ];
  body =
    "implies (target q size) (q = Queue (front q, rear q) && length (front q) \
     = size && 0 <= length (rear q) && length (rear q) < size)";
}]

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {r:queue | target r size}";
       universals = [ "size" ];
       witness_relation = "true";
     }] batched_queue_port (size : int) : queue =
  let nr = int_range_inc 0 size in
  let f = seq_gen size in
  let r = seq_gen nr in
  Queue (f, r)

let runtime_examples (_unit : unit) =
  target (batched_queue_port 4) 4 && not (target (batched_queue_port 0) 0)
