(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/quickcheck/SizedHeap.ml. *)

type heap = Empty | Heap_node of int * heap * heap
type heap_case = Heap_case of int * int * heap

let max_int left right = if left >= right then left else right

let rec depth value =
  match value with
  | Empty -> 0
  | Heap_node (_, left, right) -> 1 + max_int (depth left) (depth right)

let rec heap_below value maximum =
  match value with
  | Empty -> true
  | Heap_node (key, left, right) ->
      key < maximum && heap_below left key && heap_below right key

let[@refined.predicate] bounded_heap (value : heap) (bound : int)
    (maximum : int) : bool =
  bound >= 0 && depth value <= bound && heap_below value maximum

let[@refined.predicate] valid_heap_case (case : heap_case) : bool =
  match case with
  | Heap_case (bound, maximum, value) -> bounded_heap value bound maximum

let[@refined.logic] heap_key (value : heap) : int =
  match value with Empty -> 0 | Heap_node (key, _, _) -> key

let[@refined.logic] heap_left (value : heap) : heap =
  match value with Empty -> Empty | Heap_node (_, left, _) -> left

let[@refined.logic] heap_right (value : heap) : heap =
  match value with Empty -> Empty | Heap_node (_, _, right) -> right

let[@refined.logic] case_bound (case : heap_case) : int =
  match case with Heap_case (bound, _, _) -> bound

let[@refined.logic] case_maximum (case : heap_case) : int =
  match case with Heap_case (_, maximum, _) -> maximum

let[@refined.logic] case_heap (case : heap_case) : heap =
  match case with Heap_case (_, _, value) -> value

[@@@refined.axiom
{
  name = "heap_empty";
  quantifiers =
    [ ("forall", "bound", "int"); ("forall", "maximum", "int") ];
  body = "implies (bound >= 0) (bounded_heap Empty bound maximum)";
}]

[@@@refined.axiom
{
  name = "heap_node_intro";
  quantifiers =
    [
      ("forall", "bound", "int");
      ("forall", "maximum", "int");
      ("forall", "key", "int");
      ("forall", "left", "heap");
      ("forall", "right", "heap");
    ];
  body =
    "implies (bound > 0 && key < maximum && bounded_heap left (bound - 1) key \
     && bounded_heap right (bound - 1) key) (bounded_heap (Heap_node (key, \
     left, right)) bound maximum)";
}]

[@@@refined.axiom
{
  name = "heap_elim";
  quantifiers =
    [
      ("forall", "value", "heap");
      ("forall", "bound", "int");
      ("forall", "maximum", "int");
    ];
  body =
    "implies (bounded_heap value bound maximum) (bound >= 0 && (value = Empty \
     || (bound > 0 && value = Heap_node (heap_key value, heap_left value, \
     heap_right value) && heap_key value < maximum && bounded_heap (heap_left \
     value) (bound - 1) (heap_key value) && bounded_heap (heap_right value) \
     (bound - 1) (heap_key value))))";
}]

[@@@refined.axiom
{
  name = "heap_case_intro";
  quantifiers =
    [
      ("forall", "bound", "int");
      ("forall", "maximum", "int");
      ("forall", "value", "heap");
    ];
  body =
    "implies (bounded_heap value bound maximum) (valid_heap_case (Heap_case \
     (bound, maximum, value)))";
}]

[@@@refined.axiom
{
  name = "heap_case_elim";
  quantifiers = [ ("forall", "case", "heap_case") ];
  body =
    "implies (valid_heap_case case) (case = Heap_case (case_bound case, \
     case_maximum case, case_heap case) && bounded_heap (case_heap case) \
     (case_bound case) (case_maximum case))";
}]

let[@refined.choose] choose_heap (left : heap) (_right : heap) : heap = left

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> maximum:int -> key:int -> \
          left:heap -> right:heap -> {result:heap_case | valid_heap_case \
          result}";
       witness_relation =
         "result = Heap_case (bound, maximum, case_heap result) && (case_heap \
          result = Empty || (bound > 0 && case_heap result = Heap_node (key, \
          left, right) && key < maximum && bounded_heap left (bound - 1) key && \
          bounded_heap right (bound - 1) key))";
     }] sized_heap_port (bound : int) (maximum : int) (key : int) (left : heap)
    (right : heap) : heap_case =
  Heap_case
    (bound, maximum, choose_heap Empty (Heap_node (key, left, right)))

let runtime_examples (_unit : unit) =
  let valid = Heap_node (7, Heap_node (3, Empty, Empty), Empty) in
  let wrong_order = Heap_node (7, Heap_node (9, Empty, Empty), Empty) in
  valid_heap_case (Heap_case (2, 10, valid))
  && not (valid_heap_case (Heap_case (1, 10, valid)))
  && not (valid_heap_case (Heap_case (2, 10, wrong_order)))
