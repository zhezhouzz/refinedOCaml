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
      lower < key && key < upper && between_bst left lower key
      && between_bst right key upper

let[@refined.predicate] bst_bounded (value : tree) (bound : int) (lower : int)
    (upper : int) : bool =
  bound >= 0 && lower < upper
  && depth value <= bound
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

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.coverage
     {
       type_ =
         "lower:int -> upper:{upper:int | lower <= upper} -> {r:int | lower <= \
          r && r <= upper}";
       universals = [ "lower"; "upper" ];
       witness_relation = "true";
     }] int_range_inc (lower : int) (upper : int) : int =
  let x = int_gen () in
  if x < lower then lower else if x > upper then upper else x

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> difference:int -> lower:int -> \
          upper:{upper:int | lower < upper} -> {r:tree | bst_bounded r bound \
          lower upper}";
       universals = [ "bound"; "difference"; "lower"; "upper" ];
       witness_relation = "true";
     }]
   [@refined.measure "bound"] rec unbalanced_set_port (bound : int)
    (difference : int) (lower : int) (upper : int) : tree =
  if bound = 0 then Leaf
  else if bool_gen () then Leaf
  else if lower + 1 < upper then
    let key = int_range_inc (lower + 1) (upper - 1) in
    let left = unbalanced_set_port (bound - 1) (key - lower) lower key in
    let right = unbalanced_set_port (bound - 1) (upper - key) key upper in
    Node (key, left, right)
  else raise Reject

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> lower:int -> upper:{upper:int | \
          lower < upper} -> {r:tree | bst_bounded r bound lower upper}";
       universals = [ "bound"; "lower"; "upper" ];
       witness_relation = "true";
     }]
   [@refined.measure "bound"] rec sized_bst_port (bound : int) (lower : int)
    (upper : int) : tree =
  if bound = 0 then Leaf
  else if bool_gen () then Leaf
  else if lower + 1 < upper then
    let key = int_range_inc (lower + 1) (upper - 1) in
    let left = sized_bst_port (bound - 1) lower key in
    let right = sized_bst_port (bound - 1) key upper in
    Node (key, left, right)
  else raise Reject

let[@refined.predicate] ranged_bst (v : tree) (lower : int) (upper : int) : bool
    =
  between_bst v lower upper

[@@@refined.axiom
{
  name = "ranged_elim";
  quantifiers =
    [
      ("forall", "v", "tree"); ("forall", "lo", "int"); ("forall", "hi", "int");
    ];
  body =
    "implies (ranged_bst v lo hi) (v = Leaf || (lo + 1 < hi && v = Node \
     (tree_key v, tree_left v, tree_right v) && lo < tree_key v && tree_key v \
     < hi && ranged_bst (tree_left v) lo (tree_key v) && ranged_bst \
     (tree_right v) (tree_key v) hi))";
}]

let[@refined.coverage
     {
       type_ =
         "difference:{difference:int | difference >= 0} -> lower:int -> \
          upper:{upper:int | upper = lower + difference} -> {r:tree | \
          ranged_bst r lower upper}";
       universals = [ "difference"; "lower"; "upper" ];
       witness_relation = "true";
     }]
   [@refined.measure "difference"] rec sized_set_port (difference : int)
    (lower : int) (upper : int) : tree =
  if upper <= 1 + lower then Leaf
  else if bool_gen () then Leaf
  else
    let key = int_range_inc (lower + 1) (upper - 1) in
    let left = sized_set_port (key - lower) lower key in
    let right = sized_set_port (upper - key) key upper in
    Node (key, left, right)

let runtime_examples (_unit : unit) =
  ranged_bst (sized_set_port 8 0 8) 0 8
  && bst_bounded (sized_bst_port 1 0 8) 1 0 8
  && bst_bounded (unbalanced_set_port 1 8 0 8) 1 0 8
