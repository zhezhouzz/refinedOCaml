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
{
  name = "complete_elim";
  quantifiers = [ ("forall", "value", "tree"); ("forall", "expected", "int") ];
  body =
    "implies (complete_exact value expected) ((expected = 0 && value = Leaf) \
     || (expected > 0 && value = Node (tree_key value, tree_left value, \
     tree_right value) && complete_exact (tree_left value) (expected - 1) && \
     complete_exact (tree_right value) (expected - 1)))";
}]

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> {r:tree | complete_exact r bound}";
       universals = [ "bound" ];
     }]
   [@refined.measure "bound"] rec complete_tree_port (bound : int) : tree =
  if bound = 0 then Leaf
  else
    let key = int_gen () in
    let left = complete_tree_port (bound - 1) in
    let right = complete_tree_port (bound - 1) in
    Node (key, left, right)

let runtime_examples (_unit : unit) = complete_exact (complete_tree_port 3) 3
