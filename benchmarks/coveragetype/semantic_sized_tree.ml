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
  name = "sized_elim";
  quantifiers = [ ("forall", "value", "tree"); ("forall", "bound", "int") ];
  body =
    "implies (bound >= 0 && depth_bounded value bound) (value = Leaf || (bound \
     > 0 && value = Node (tree_key value, tree_left value, tree_right value) \
     && depth_bounded (tree_left value) (bound - 1) && depth_bounded \
     (tree_right value) (bound - 1)))";
}]

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> {r:tree | depth_bounded r bound}";
       universals = [ "bound" ];
     }]
   [@refined.measure "bound"] rec sized_tree_port (bound : int) : tree =
  if bound = 0 then Leaf
  else if bool_gen () then Leaf
  else
    let key = int_gen () in
    let left = sized_tree_port (bound - 1) in
    let right = sized_tree_port (bound - 1) in
    Node (key, left, right)

let runtime_examples (_unit : unit) = depth_bounded (sized_tree_port 3) 3
