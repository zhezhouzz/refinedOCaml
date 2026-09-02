(* SPDX-License-Identifier: MIT
   Semantic ports of the bounded search-tree generators in CoverageType. *)

type tree = Leaf | Node of int * tree * tree
type tree_case = Tree_case of int * int * int * tree

let max_int left right = if left >= right then left else right

let rec depth value =
  match value with
  | Leaf -> 0
  | Node (_, left, right) -> 1 + max_int (depth left) (depth right)

let rec between_bst value lower upper =
  match value with
  | Leaf -> true
  | Node (key, left, right) ->
      lower < key && key < upper
      && between_bst left lower key
      && between_bst right key upper

let[@refined.predicate] bst_bounded (value : tree) (bound : int) (lower : int)
    (upper : int) : bool =
  bound >= 0 && lower < upper && depth value <= bound
  && between_bst value lower upper

let[@refined.predicate] valid_bst_case (case : tree_case) : bool =
  match case with
  | Tree_case (bound, lower, upper, value) ->
      bst_bounded value bound lower upper

let[@refined.predicate] valid_set_case (case : tree_case) : bool =
  match case with
  | Tree_case (bound, lower, upper, value) ->
      upper = lower + bound && bst_bounded value bound lower upper

let[@refined.logic] tree_key (value : tree) : int =
  match value with Leaf -> 0 | Node (key, _, _) -> key

let[@refined.logic] tree_left (value : tree) : tree =
  match value with Leaf -> Leaf | Node (_, left, _) -> left

let[@refined.logic] tree_right (value : tree) : tree =
  match value with Leaf -> Leaf | Node (_, _, right) -> right

let[@refined.logic] case_bound (case : tree_case) : int =
  match case with Tree_case (bound, _, _, _) -> bound

let[@refined.logic] case_lower (case : tree_case) : int =
  match case with Tree_case (_, lower, _, _) -> lower

let[@refined.logic] case_upper (case : tree_case) : int =
  match case with Tree_case (_, _, upper, _) -> upper

let[@refined.logic] case_tree (case : tree_case) : tree =
  match case with Tree_case (_, _, _, value) -> value

[@@@refined.axiom
{
  name = "bst_leaf";
  quantifiers =
    [
      ("forall", "bound", "int");
      ("forall", "lower", "int");
      ("forall", "upper", "int");
    ];
  body =
    "implies (bound >= 0 && lower < upper) (bst_bounded Leaf bound lower \
     upper)";
}]

[@@@refined.axiom
{
  name = "bst_node_intro";
  quantifiers =
    [
      ("forall", "bound", "int");
      ("forall", "lower", "int");
      ("forall", "upper", "int");
      ("forall", "key", "int");
      ("forall", "left", "tree");
      ("forall", "right", "tree");
    ];
  body =
    "implies (bound > 0 && lower < key && key < upper && bst_bounded left \
     (bound - 1) lower key && bst_bounded right (bound - 1) key upper) \
     (bst_bounded (Node (key, left, right)) bound lower upper)";
}]

[@@@refined.axiom
{
  name = "bst_elim";
  quantifiers =
    [
      ("forall", "value", "tree");
      ("forall", "bound", "int");
      ("forall", "lower", "int");
      ("forall", "upper", "int");
    ];
  body =
    "implies (bst_bounded value bound lower upper) (bound >= 0 && lower < \
     upper && (value = Leaf || (bound > 0 && value = Node (tree_key value, \
     tree_left value, tree_right value) && lower < tree_key value && tree_key \
     value < upper && bst_bounded (tree_left value) (bound - 1) lower \
     (tree_key value) && bst_bounded (tree_right value) (bound - 1) (tree_key \
     value) upper)))";
}]

[@@@refined.axiom
{
  name = "bst_case_intro";
  quantifiers =
    [
      ("forall", "bound", "int");
      ("forall", "lower", "int");
      ("forall", "upper", "int");
      ("forall", "value", "tree");
    ];
  body =
    "implies (bst_bounded value bound lower upper) (valid_bst_case (Tree_case \
     (bound, lower, upper, value)))";
}]

[@@@refined.axiom
{
  name = "bst_case_elim";
  quantifiers = [ ("forall", "case", "tree_case") ];
  body =
    "implies (valid_bst_case case) (case = Tree_case (case_bound case, \
     case_lower case, case_upper case, case_tree case) && bst_bounded \
     (case_tree case) (case_bound case) (case_lower case) (case_upper case))";
}]

[@@@refined.axiom
{
  name = "set_case_intro";
  quantifiers =
    [
      ("forall", "bound", "int");
      ("forall", "lower", "int");
      ("forall", "upper", "int");
      ("forall", "value", "tree");
    ];
  body =
    "implies (upper = lower + bound && bst_bounded value bound lower upper) \
     (valid_set_case (Tree_case (bound, lower, upper, value)))";
}]

[@@@refined.axiom
{
  name = "set_case_elim";
  quantifiers = [ ("forall", "case", "tree_case") ];
  body =
    "implies (valid_set_case case) (case = Tree_case (case_bound case, \
     case_lower case, case_upper case, case_tree case) && case_upper case = \
     case_lower case + case_bound case && bst_bounded (case_tree case) \
     (case_bound case) (case_lower case) (case_upper case))";
}]

let[@refined.choose] choose_tree (left : tree) (_right : tree) : tree = left

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> difference:int -> lower:int -> \
          upper:{upper:int | lower < upper} -> key:int -> left:tree -> \
          right:tree -> {result:tree_case | valid_bst_case result}";
       witness_relation =
         "result = Tree_case (bound, lower, upper, case_tree result) && \
          (case_tree result = Leaf || (bound > 0 && case_tree result = Node \
          (key, left, right) && lower < key && key < upper && bst_bounded left \
          (bound - 1) lower key && bst_bounded right (bound - 1) key upper))";
     }] unbalanced_set_port (bound : int) (difference : int) (lower : int)
    (upper : int) (key : int) (left : tree) (right : tree) : tree_case =
  let _unused_difference = difference in
  Tree_case (bound, lower, upper, choose_tree Leaf (Node (key, left, right)))

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> lower:int -> upper:{upper:int | \
          lower < upper} -> key:int -> left:tree -> right:tree -> \
          {result:tree_case | valid_bst_case result}";
       witness_relation =
         "result = Tree_case (bound, lower, upper, case_tree result) && \
          (case_tree result = Leaf || (bound > 0 && case_tree result = Node \
          (key, left, right) && lower < key && key < upper && bst_bounded left \
          (bound - 1) lower key && bst_bounded right (bound - 1) key upper))";
     }] sized_bst_port (bound : int) (lower : int) (upper : int) (key : int)
    (left : tree) (right : tree) : tree_case =
  Tree_case (bound, lower, upper, choose_tree Leaf (Node (key, left, right)))

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> lower:int -> upper:{upper:int | \
          upper = lower + bound} -> key:int -> left:tree -> right:tree -> \
          {result:tree_case | valid_set_case result}";
       witness_relation =
         "result = Tree_case (bound, lower, upper, case_tree result) && \
          (case_tree result = Leaf || (bound > 0 && case_tree result = Node \
          (key, left, right) && lower < key && key < upper && bst_bounded left \
          (bound - 1) lower key && bst_bounded right (bound - 1) key upper))";
     }] sized_set_port (bound : int) (lower : int) (upper : int) (key : int)
    (left : tree) (right : tree) : tree_case =
  Tree_case (bound, lower, upper, choose_tree Leaf (Node (key, left, right)))

let runtime_examples (_unit : unit) =
  let valid = Node (4, Node (2, Leaf, Leaf), Node (7, Leaf, Leaf)) in
  let wrong_order = Node (4, Node (5, Leaf, Leaf), Node (7, Leaf, Leaf)) in
  valid_bst_case (Tree_case (2, 0, 10, valid))
  && not (valid_bst_case (Tree_case (1, 0, 10, valid)))
  && not (valid_bst_case (Tree_case (2, 0, 10, wrong_order)))
  && valid_set_case (Tree_case (10, 0, 10, valid))
  && not (valid_set_case (Tree_case (9, 0, 10, valid)))
