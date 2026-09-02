(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/quickchick/SizedTree.ml. *)

type tree = Leaf | Node of int * tree * tree
type sized_case = Sized_case of int * tree

let max_int left right = if left >= right then left else right

let rec depth value =
  match value with
  | Leaf -> 0
  | Node (_, left, right) -> 1 + max_int (depth left) (depth right)

let[@refined.predicate] depth_bounded (value : tree) (bound : int) : bool =
  depth value <= bound

let[@refined.predicate] valid_sized_tree (case : sized_case) : bool =
  match case with
  | Sized_case (bound, value) -> bound >= 0 && depth_bounded value bound

let[@refined.logic] tree_key (value : tree) : int =
  match value with Leaf -> 0 | Node (key, _, _) -> key

let[@refined.logic] tree_left (value : tree) : tree =
  match value with Leaf -> Leaf | Node (_, left, _) -> left

let[@refined.logic] tree_right (value : tree) : tree =
  match value with Leaf -> Leaf | Node (_, _, right) -> right

let[@refined.logic] case_bound (case : sized_case) : int =
  match case with Sized_case (bound, _) -> bound

let[@refined.logic] case_tree (case : sized_case) : tree =
  match case with Sized_case (_, value) -> value

[@@@refined.axiom
{
  name = "sized_leaf";
  quantifiers = [ ("forall", "bound", "int") ];
  body = "implies (bound >= 0) (depth_bounded Leaf bound)";
}]

[@@@refined.axiom
{
  name = "sized_node_intro";
  quantifiers =
    [
      ("forall", "bound", "int");
      ("forall", "key", "int");
      ("forall", "left", "tree");
      ("forall", "right", "tree");
    ];
  body =
    "implies (bound > 0 && depth_bounded left (bound - 1) && depth_bounded \
     right (bound - 1)) (depth_bounded (Node (key, left, right)) bound)";
}]

[@@@refined.axiom
{
  name = "sized_elim";
  quantifiers =
    [ ("forall", "value", "tree"); ("forall", "bound", "int") ];
  body =
    "implies (bound >= 0 && depth_bounded value bound) (value = Leaf || (bound \
     > 0 && value = Node (tree_key value, tree_left value, tree_right value) && \
     depth_bounded (tree_left value) (bound - 1) && depth_bounded (tree_right \
     value) (bound - 1)))";
}]

[@@@refined.axiom
{
  name = "sized_case_intro";
  quantifiers =
    [ ("forall", "bound", "int"); ("forall", "value", "tree") ];
  body =
    "implies (bound >= 0 && depth_bounded value bound) (valid_sized_tree \
     (Sized_case (bound, value)))";
}]

[@@@refined.axiom
{
  name = "sized_case_elim";
  quantifiers = [ ("forall", "case", "sized_case") ];
  body =
    "implies (valid_sized_tree case) (case = Sized_case (case_bound case, \
     case_tree case) && case_bound case >= 0 && depth_bounded (case_tree case) \
     (case_bound case))";
}]

let[@refined.choose] choose_tree (left : tree) (_right : tree) : tree = left

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> key:int -> left:tree -> \
          right:tree -> {result:sized_case | valid_sized_tree result}";
       witness_relation =
         "result = Sized_case (bound, case_tree result) && (case_tree result = \
          Leaf || (bound > 0 && case_tree result = Node (key, left, right) && \
          depth_bounded left (bound - 1) && depth_bounded right (bound - 1)))";
     }] sized_tree_port (bound : int) (key : int) (left : tree) (right : tree) :
    sized_case =
  Sized_case (bound, choose_tree Leaf (Node (key, left, right)))

let runtime_examples (_unit : unit) =
  let two = Node (1, Node (2, Leaf, Leaf), Leaf) in
  valid_sized_tree (Sized_case (2, two))
  && not (valid_sized_tree (Sized_case (1, two)))
