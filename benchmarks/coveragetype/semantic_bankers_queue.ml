(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/elrond/BankersQueue.ml. *)

type front_stream = FNil | FCons of int * front_stream
type rear_list = RNil | RCons of int * rear_list
type queue_case = Queue_case of int * front_stream * rear_list

let rec front_length value =
  match value with FNil -> 0 | FCons (_, tail) -> 1 + front_length tail

let rec rear_length value =
  match value with RNil -> 0 | RCons (_, tail) -> 1 + rear_length tail

let[@refined.predicate] front_sized (value : front_stream) (size : int) : bool =
  front_length value = size

let[@refined.predicate] rear_shorter (value : rear_list) (bound : int) : bool =
  rear_length value < bound

let[@refined.predicate] valid_bankers_queue (case : queue_case) : bool =
  match case with
  | Queue_case (front_size, front, rear) ->
      front_size >= 0
      && front_sized front front_size
      && rear_shorter rear front_size

let[@refined.logic] front_head (value : front_stream) : int =
  match value with FNil -> 0 | FCons (head, _) -> head

let[@refined.logic] front_tail (value : front_stream) : front_stream =
  match value with FNil -> FNil | FCons (_, tail) -> tail

let[@refined.logic] rear_head (value : rear_list) : int =
  match value with RNil -> 0 | RCons (head, _) -> head

let[@refined.logic] rear_tail (value : rear_list) : rear_list =
  match value with RNil -> RNil | RCons (_, tail) -> tail

let[@refined.logic] queue_size (case : queue_case) : int =
  match case with Queue_case (size, _, _) -> size

let[@refined.logic] queue_front (case : queue_case) : front_stream =
  match case with Queue_case (_, front, _) -> front

let[@refined.logic] queue_rear (case : queue_case) : rear_list =
  match case with Queue_case (_, _, rear) -> rear

[@@@refined.axiom
{
  name = "front_nil";
  quantifiers = [];
  body = "front_sized FNil 0";
}]

[@@@refined.axiom
{
  name = "front_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "front_stream");
      ("forall", "tail_size", "int");
    ];
  body =
    "implies (front_sized tail tail_size) (front_sized (FCons (head, tail)) \
     (tail_size + 1))";
}]

[@@@refined.axiom
{
  name = "front_elim";
  quantifiers =
    [ ("forall", "value", "front_stream"); ("forall", "size", "int") ];
  body =
    "implies (front_sized value size) ((size = 0 && value = FNil) || (size > \
     0 && value = FCons (front_head value, front_tail value) && front_sized \
     (front_tail value) (size - 1)))";
}]

[@@@refined.axiom
{
  name = "rear_nil";
  quantifiers = [ ("forall", "bound", "int") ];
  body = "implies (bound > 0) (rear_shorter RNil bound)";
}]

[@@@refined.axiom
{
  name = "rear_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "rear_list");
      ("forall", "bound", "int");
    ];
  body =
    "implies (bound > 1 && rear_shorter tail (bound - 1)) (rear_shorter \
     (RCons (head, tail)) bound)";
}]

[@@@refined.axiom
{
  name = "rear_elim";
  quantifiers =
    [ ("forall", "value", "rear_list"); ("forall", "bound", "int") ];
  body =
    "implies (rear_shorter value bound) (bound > 0 && (value = RNil || (bound \
     > 1 && value = RCons (rear_head value, rear_tail value) && rear_shorter \
     (rear_tail value) (bound - 1))))";
}]

[@@@refined.axiom
{
  name = "bankers_intro";
  quantifiers =
    [
      ("forall", "size", "int");
      ("forall", "front", "front_stream");
      ("forall", "rear", "rear_list");
    ];
  body =
    "implies (size >= 0 && front_sized front size && rear_shorter rear size) \
     (valid_bankers_queue (Queue_case (size, front, rear)))";
}]

[@@@refined.axiom
{
  name = "bankers_elim";
  quantifiers = [ ("forall", "case", "queue_case") ];
  body =
    "implies (valid_bankers_queue case) (case = Queue_case (queue_size case, \
     queue_front case, queue_rear case) && queue_size case >= 0 && \
     front_sized (queue_front case) (queue_size case) && rear_shorter \
     (queue_rear case) (queue_size case))";
}]

let[@refined.choose] choose_front (left : front_stream)
    (_right : front_stream) : front_stream =
  left

let[@refined.choose] choose_rear (left : rear_list) (_right : rear_list) :
    rear_list =
  left

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> front_head_value:int -> \
          front_tail_value:front_stream -> rear_head_value:int -> \
          rear_tail_value:rear_list -> {result:queue_case | \
          valid_bankers_queue result}";
       witness_relation =
         "result = Queue_case (size, queue_front result, queue_rear result) && \
          ((size = 0 && queue_front result = FNil) || (size > 0 && queue_front \
          result = FCons (front_head_value, front_tail_value) && front_sized \
          front_tail_value (size - 1))) && (queue_rear result = RNil || (size > \
          1 && queue_rear result = RCons (rear_head_value, rear_tail_value) && \
          rear_shorter rear_tail_value (size - 1)))";
     }] bankers_queue_port (size : int) (front_head_value : int)
    (front_tail_value : front_stream) (rear_head_value : int)
    (rear_tail_value : rear_list) : queue_case =
  Queue_case
    ( size,
      choose_front FNil (FCons (front_head_value, front_tail_value)),
      choose_rear RNil (RCons (rear_head_value, rear_tail_value)) )

let runtime_examples (_unit : unit) =
  let front = FCons (1, FCons (2, FCons (3, FNil))) in
  let valid_rear = RCons (4, RCons (5, RNil)) in
  let long_rear = RCons (4, RCons (5, RCons (6, RNil))) in
  valid_bankers_queue (Queue_case (3, front, valid_rear))
  && not (valid_bankers_queue (Queue_case (2, front, valid_rear)))
  && not (valid_bankers_queue (Queue_case (3, front, long_rear)))
