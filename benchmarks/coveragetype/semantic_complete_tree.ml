(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/leonidas/CompleteTree.ml. *)

type tree = Leaf | Node of int * tree * tree
type complete_case = Complete_case of int * tree

let max_int left right = if left >= right then left else right

let rec depth value =
  match value with
  | Leaf -> 0
  | Node (_, left, right) -> 1 + max_int (depth left) (depth right)

let rec complete value =
  match value with
  | Leaf -> true
  | Node (_, left, right) ->
      complete left && complete right && depth left = depth right

let[@refined.predicate] complete_exact (value : tree) (expected : int) : bool =
  complete value && depth value = expected

let[@refined.predicate] valid_complete_case (case : complete_case) : bool =
  match case with
  | Complete_case (expected, value) -> complete_exact value expected

let[@refined.logic] tree_key (value : tree) : int =
  match value with Leaf -> 0 | Node (key, _, _) -> key

let[@refined.logic] tree_left (value : tree) : tree =
  match value with Leaf -> Leaf | Node (_, left, _) -> left

let[@refined.logic] tree_right (value : tree) : tree =
  match value with Leaf -> Leaf | Node (_, _, right) -> right

let[@refined.logic] case_depth (case : complete_case) : int =
  match case with Complete_case (expected, _) -> expected

let[@refined.logic] case_tree (case : complete_case) : tree =
  match case with Complete_case (_, value) -> value

[@@@refined.axiom
{ name = "complete_leaf"; quantifiers = []; body = "complete_exact Leaf 0" }]

[@@@refined.axiom
{
  name = "complete_node_intro";
  quantifiers =
    [
      ("forall", "expected", "int");
      ("forall", "key", "int");
      ("forall", "left", "tree");
      ("forall", "right", "tree");
    ];
  body =
    "implies (expected > 0 && complete_exact left (expected - 1) && \
     complete_exact right (expected - 1)) (complete_exact (Node (key, left, \
     right)) expected)";
}]

[@@@refined.axiom
{
  name = "complete_elim";
  quantifiers = [ ("forall", "value", "tree"); ("forall", "expected", "int") ];
  body =
    "implies (complete_exact value expected) ((expected = 0 && value = Leaf) \
     || (expected > 0 && value = Node (tree_key value, tree_left value, \
     tree_right value) && complete_exact (tree_left value) (expected - 1) && \
     complete_exact (tree_right value) (expected - 1)))";
}]

[@@@refined.axiom
{
  name = "complete_case_intro";
  quantifiers = [ ("forall", "expected", "int"); ("forall", "value", "tree") ];
  body =
    "implies (complete_exact value expected) (valid_complete_case \
     (Complete_case (expected, value)))";
}]

[@@@refined.axiom
{
  name = "complete_case_elim";
  quantifiers = [ ("forall", "case", "complete_case") ];
  body =
    "implies (valid_complete_case case) (case = Complete_case (case_depth \
     case, case_tree case) && complete_exact (case_tree case) (case_depth \
     case))";
}]

let[@refined.choose] choose_tree (left : tree) (_right : tree) : tree = left

let[@refined.coverage
     {
       type_ =
         "expected:{expected:int | expected >= 0} -> key:int -> left:tree -> \
          right:tree -> {result:complete_case | valid_complete_case result}";
       witness_relation =
         "result = Complete_case (expected, case_tree result) && ((expected = \
          0 && case_tree result = Leaf) || (expected > 0 && case_tree result = \
          Node (key, left, right) && complete_exact left (expected - 1) && \
          complete_exact right (expected - 1)))";
     }] complete_tree_port (expected : int) (key : int) (left : tree)
    (right : tree) : complete_case =
  Complete_case (expected, choose_tree Leaf (Node (key, left, right)))

let runtime_examples (_unit : unit) =
  let leaf = Leaf in
  let full = Node (1, Node (2, leaf, leaf), Node (3, leaf, leaf)) in
  let incomplete = Node (1, Node (2, leaf, leaf), leaf) in
  valid_complete_case (Complete_case (2, full))
  && (not (valid_complete_case (Complete_case (1, full))))
  && not (valid_complete_case (Complete_case (2, incomplete)))
