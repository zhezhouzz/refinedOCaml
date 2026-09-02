(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/elrond/BatchedQueue.ml. *)

type ilist = Nil | Cons of int * ilist
type queue_case = Queue_case of int * ilist * ilist

let rec length value =
  match value with Nil -> 0 | Cons (_, tail) -> 1 + length tail

let[@refined.predicate] exact_size (value : ilist) (size : int) : bool =
  length value = size

let[@refined.predicate] shorter (value : ilist) (bound : int) : bool =
  length value < bound

let[@refined.predicate] valid_batched_queue (case : queue_case) : bool =
  match case with
  | Queue_case (size, front, rear) ->
      size >= 0 && exact_size front size && shorter rear size

let[@refined.logic] list_head (value : ilist) : int =
  match value with Nil -> 0 | Cons (head, _) -> head

let[@refined.logic] list_tail (value : ilist) : ilist =
  match value with Nil -> Nil | Cons (_, tail) -> tail

let[@refined.logic] queue_size (case : queue_case) : int =
  match case with Queue_case (size, _, _) -> size

let[@refined.logic] queue_front (case : queue_case) : ilist =
  match case with Queue_case (_, front, _) -> front

let[@refined.logic] queue_rear (case : queue_case) : ilist =
  match case with Queue_case (_, _, rear) -> rear

[@@@refined.axiom
{ name = "exact_nil"; quantifiers = []; body = "exact_size Nil 0" }]

[@@@refined.axiom
{
  name = "exact_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "ilist");
      ("forall", "tail_size", "int");
    ];
  body =
    "implies (exact_size tail tail_size) (exact_size (Cons (head, tail)) \
     (tail_size + 1))";
}]

[@@@refined.axiom
{
  name = "exact_elim";
  quantifiers = [ ("forall", "value", "ilist"); ("forall", "size", "int") ];
  body =
    "implies (exact_size value size) ((size = 0 && value = Nil) || (size > 0 \
     && value = Cons (list_head value, list_tail value) && exact_size \
     (list_tail value) (size - 1)))";
}]

[@@@refined.axiom
{
  name = "shorter_nil";
  quantifiers = [ ("forall", "bound", "int") ];
  body = "implies (bound > 0) (shorter Nil bound)";
}]

[@@@refined.axiom
{
  name = "shorter_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "ilist");
      ("forall", "bound", "int");
    ];
  body =
    "implies (bound > 1 && shorter tail (bound - 1)) (shorter (Cons (head, \
     tail)) bound)";
}]

[@@@refined.axiom
{
  name = "shorter_elim";
  quantifiers = [ ("forall", "value", "ilist"); ("forall", "bound", "int") ];
  body =
    "implies (shorter value bound) (bound > 0 && (value = Nil || (bound > 1 && \
     value = Cons (list_head value, list_tail value) && shorter (list_tail \
     value) (bound - 1))))";
}]

[@@@refined.axiom
{
  name = "batched_intro";
  quantifiers =
    [
      ("forall", "size", "int");
      ("forall", "front", "ilist");
      ("forall", "rear", "ilist");
    ];
  body =
    "implies (size >= 0 && exact_size front size && shorter rear size) \
     (valid_batched_queue (Queue_case (size, front, rear)))";
}]

[@@@refined.axiom
{
  name = "batched_elim";
  quantifiers = [ ("forall", "case", "queue_case") ];
  body =
    "implies (valid_batched_queue case) (case = Queue_case (queue_size case, \
     queue_front case, queue_rear case) && queue_size case >= 0 && exact_size \
     (queue_front case) (queue_size case) && shorter (queue_rear case) \
     (queue_size case))";
}]

let[@refined.choose] choose_list (left : ilist) (_right : ilist) : ilist = left

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> front_head:int -> front_tail:ilist -> \
          rear_head:int -> rear_tail:ilist -> {result:queue_case | \
          valid_batched_queue result}";
       witness_relation =
         "result = Queue_case (size, queue_front result, queue_rear result) && \
          ((size = 0 && queue_front result = Nil) || (size > 0 && queue_front \
          result = Cons (front_head, front_tail) && exact_size front_tail \
          (size - 1))) && (queue_rear result = Nil || (size > 1 && queue_rear \
          result = Cons (rear_head, rear_tail) && shorter rear_tail (size - \
          1)))";
     }] batched_queue_port (size : int) (front_head : int) (front_tail : ilist)
    (rear_head : int) (rear_tail : ilist) : queue_case =
  Queue_case
    ( size,
      choose_list Nil (Cons (front_head, front_tail)),
      choose_list Nil (Cons (rear_head, rear_tail)) )

let runtime_examples (_unit : unit) =
  let front = Cons (1, Cons (2, Cons (3, Nil))) in
  let valid_rear = Cons (4, Cons (5, Nil)) in
  let long_rear = Cons (4, Cons (5, Cons (6, Nil))) in
  valid_batched_queue (Queue_case (3, front, valid_rear))
  && (not (valid_batched_queue (Queue_case (2, front, valid_rear))))
  && not (valid_batched_queue (Queue_case (3, front, long_rear)))
