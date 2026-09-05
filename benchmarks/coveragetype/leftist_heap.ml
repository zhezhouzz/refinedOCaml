(* SPDX-License-Identifier: MIT
   Recursive generator port of data/PLDI23/elrond/LeftistHeap.ml at the revision pinned in
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
{
  name = "leftist_depth_elim";
  quantifiers = [ ("forall", "value", "heap"); ("forall", "expected", "int") ];
  body =
    "implies (leftist_depth value expected) ((expected = 0 && value = Empty) \
     || (expected > 0 && value = Node (heap_rank value, heap_key value, \
     heap_left value, heap_right value) && leftist_depth (heap_left value) \
     (expected - 1) && leftist_depth (heap_right value) (heap_depth \
     (heap_right value)) && 0 <= heap_depth (heap_right value) && heap_depth \
     (heap_right value) < expected && heap_rank value = heap_depth (heap_right \
     value) + 1))";
}]

let[@refined.choose] int_gen (_unit : unit) : int = 0

(* Clamping havoc preserves the output set of upstream int_range_inc. *)
let[@refined.coverage
     {
       type_ =
         "lower:int -> upper:{upper:int | upper >= lower} -> {r:int | lower <= \
          r && r <= upper}";
       universals = [ "lower"; "upper" ];
     }] int_range_inc (lower : int) (upper : int) : int =
  let candidate = int_gen () in
  if candidate < lower then lower
  else if candidate > upper then upper
  else candidate

let[@refined.coverage
     {
       type_ =
         "expected:{expected:int | expected >= 0} -> {result:heap | \
          leftist_depth result expected}";
       universals = [ "expected" ];
     }]
   [@refined.measure "expected"] rec generate (expected : int) : heap =
  if expected = 0 then Empty
  else
    let left_depth = expected - 1 in
    let left = generate left_depth in
    let right_depth = int_range_inc 0 left_depth in
    let right = generate right_depth in
    Node (right_depth + 1, int_gen (), left, right)

let runtime_examples (_unit : unit) =
  let leaf = Empty in
  let singleton = Node (1, 7, leaf, leaf) in
  let left_child = Node (1, 3, leaf, leaf) in
  let valid = Node (1, 5, left_child, leaf) in
  let invalid_rank = Node (2, 5, left_child, leaf) in
  let invalid_shape = Node (2, 5, leaf, left_child) in
  leftist_depth (generate 0) 0
  && leftist_depth (generate 4) 4
  && leftist_depth leaf 0 && leftist_depth singleton 1 && leftist_depth valid 2
  && (not (is_leftist invalid_rank))
  && not (is_leftist invalid_shape)
