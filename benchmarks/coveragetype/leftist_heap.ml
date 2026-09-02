(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/elrond/LeftistHeap.ml at the revision pinned in
   ../manifest.tsv. The executable predicate and the logical axioms describe
   the same rank/depth invariant. *)

type heap = Empty | Node of int * int * heap * heap

let max_int left right = if left >= right then left else right

let rec depth (value : heap) : int =
  match value with
  | Empty -> 0
  | Node (_, _, left, right) -> 1 + max_int (depth left) (depth right)

let rec is_leftist (value : heap) : bool =
  match value with
  | Empty -> true
  | Node (rank, _, left, right) ->
      is_leftist left && is_leftist right
      && depth left >= depth right
      && rank = depth right + 1

let[@refined.predicate] leftist (value : heap) : bool = is_leftist value

let[@refined.predicate] leftist_depth (value : heap) (expected : int) : bool =
  is_leftist value && depth value = expected

let[@refined.logic] heap_depth (value : heap) : int = depth value

let[@refined.logic] heap_rank (value : heap) : int =
  match value with Empty -> 0 | Node (rank, _, _, _) -> rank

let[@refined.logic] heap_key (value : heap) : int =
  match value with Empty -> 0 | Node (_, key, _, _) -> key

let[@refined.logic] heap_left (value : heap) : heap =
  match value with Empty -> Empty | Node (_, _, left, _) -> left

let[@refined.logic] heap_right (value : heap) : heap =
  match value with Empty -> Empty | Node (_, _, _, right) -> right

[@@@refined.axiom
{
  name = "leftist_empty_depth";
  quantifiers = [];
  body = "leftist_depth Empty 0";
}]

[@@@refined.axiom
{ name = "leftist_empty"; quantifiers = []; body = "leftist Empty" }]

[@@@refined.axiom
{
  name = "leftist_depth_nonnegative";
  quantifiers = [ ("forall", "value", "heap"); ("forall", "expected", "int") ];
  body = "implies (leftist_depth value expected) (expected >= 0)";
}]

[@@@refined.axiom
{
  name = "leftist_zero_is_empty";
  quantifiers = [ ("forall", "value", "heap") ];
  body = "implies (leftist_depth value 0) (value = Empty)";
}]

[@@@refined.axiom
{
  name = "leftist_depth_is_leftist";
  quantifiers = [ ("forall", "value", "heap"); ("forall", "expected", "int") ];
  body = "implies (leftist_depth value expected) (leftist value)";
}]

[@@@refined.axiom
{
  name = "leftist_node_intro";
  quantifiers =
    [
      ("forall", "rank", "int");
      ("forall", "key", "int");
      ("forall", "left", "heap");
      ("forall", "right", "heap");
      ("forall", "left_depth", "int");
      ("forall", "right_depth", "int");
    ];
  body =
    "implies (leftist_depth left left_depth && leftist_depth right right_depth \
     && left_depth >= right_depth && rank = right_depth + 1) (leftist_depth \
     (Node (rank, key, left, right)) (left_depth + 1))";
}]

[@@@refined.axiom
{
  name = "leftist_node_wellformed";
  quantifiers =
    [
      ("forall", "rank", "int");
      ("forall", "key", "int");
      ("forall", "left", "heap");
      ("forall", "right", "heap");
      ("forall", "left_depth", "int");
      ("forall", "right_depth", "int");
    ];
  body =
    "implies (leftist_depth left left_depth && leftist_depth right right_depth \
     && left_depth >= right_depth && rank = right_depth + 1) (leftist (Node \
     (rank, key, left, right)))";
}]

[@@@refined.axiom
{
  name = "leftist_elim";
  quantifiers = [ ("forall", "value", "heap") ];
  body =
    "implies (leftist value) (value = Empty || (value = Node (heap_rank value, \
     heap_key value, heap_left value, heap_right value) && leftist_depth \
     (heap_left value) (heap_depth (heap_left value)) && leftist_depth \
     (heap_right value) (heap_depth (heap_right value)) && heap_depth \
     (heap_left value) >= heap_depth (heap_right value) && heap_rank value = \
     heap_depth (heap_right value) + 1))";
}]

let[@refined.choose] choose (left : heap) (_right : heap) : heap = left

let[@refined.coverage
     {
       type_ =
         "expected:{expected:int | expected >= 0} -> rank:int -> key:int -> \
          left:heap -> right:heap -> left_depth:int -> right_depth:int -> \
          {result:heap | leftist result}";
       witness_relation =
         "(expected = 0 && result = Empty) || (expected > 0 && result = Node \
          (rank, key, left, right) && leftist_depth left left_depth && \
          leftist_depth right right_depth && left_depth >= right_depth && rank \
          = right_depth + 1 && expected = left_depth + 1)";
     }] generate (expected : int) (rank : int) (key : int) (left : heap)
    (right : heap) (left_depth : int) (right_depth : int) : heap =
  choose Empty (Node (rank, key, left, right))

let runtime_examples (_unit : unit) =
  let leaf = Empty in
  let singleton = Node (1, 7, leaf, leaf) in
  let left_child = Node (1, 3, leaf, leaf) in
  let valid = Node (1, 5, left_child, leaf) in
  let invalid_rank = Node (2, 5, left_child, leaf) in
  let invalid_shape = Node (2, 5, leaf, left_child) in
  leftist_depth leaf 0 && leftist_depth singleton 1 && leftist_depth valid 2
  && (not (is_leftist invalid_rank))
  && not (is_leftist invalid_shape)
