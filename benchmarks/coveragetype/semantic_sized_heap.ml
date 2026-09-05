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

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> maximum:int -> {r:heap | \
          bounded_heap r bound maximum}";
       universals = [ "bound"; "maximum" ];
       witness_relation = "true";
     }]
   [@refined.measure "bound"] rec sized_heap_port (bound : int) (maximum : int)
    : heap =
  if bound = 0 then Empty
  else if bool_gen () then Empty
  else
    let key = int_gen () in
    if key < maximum then
      let left = sized_heap_port (bound - 1) key in
      let right = sized_heap_port (bound - 1) key in
      Heap_node (key, left, right)
    else raise Reject

let runtime_examples (_unit : unit) =
  bounded_heap (sized_heap_port 1 1) 1 1
  &&
    try
      ignore (sized_heap_port 2 1);
      false
    with Reject -> true
