(* SPDX-License-Identifier: MIT
   Semantic port of data/PLDI23/quickchick/RedBlackTree.ml. True denotes red. *)

type rb_tree = RBLeaf | RBNode of bool * rb_tree * int * rb_tree
type rb_case = RBCase of int * bool * int * rb_tree

let root_red value =
  match value with RBLeaf -> false | RBNode (red, _, _, _) -> red

let rec black_height value =
  match value with
  | RBLeaf -> 0
  | RBNode (red, left, _, right) ->
      let left_height = black_height left in
      let right_height = black_height right in
      if left_height < 0 || left_height <> right_height then -1
      else left_height + if red then 0 else 1

let rec no_red_red value =
  match value with
  | RBLeaf -> true
  | RBNode (red, left, _, right) ->
      ((not red) || ((not (root_red left)) && not (root_red right)))
      && no_red_red left && no_red_red right

let[@refined.predicate] rb_wellformed (value : rb_tree) (height : int) : bool =
  black_height value = height && no_red_red value

let[@refined.predicate] nonred_root (value : rb_tree) : bool =
  not (root_red value)

let[@refined.predicate] root_allowed (value : rb_tree) (color : bool)
    (height : int) : bool =
  if color then not (root_red value)
  else if height = 0 then
    match value with RBLeaf -> true | RBNode (red, _, _, _) -> red
  else true

let[@refined.predicate] valid_rb_case (case : rb_case) : bool =
  match case with
  | RBCase (invariant, color, height, value) ->
      invariant >= 0 && height >= 0
      && (if color then 2 * height = invariant else (2 * height) + 1 = invariant)
      && rb_wellformed value height
      && root_allowed value color height

let[@refined.logic] rb_color (value : rb_tree) : bool =
  match value with RBLeaf -> false | RBNode (red, _, _, _) -> red

let[@refined.logic] rb_left (value : rb_tree) : rb_tree =
  match value with RBLeaf -> RBLeaf | RBNode (_, left, _, _) -> left

let[@refined.logic] rb_key (value : rb_tree) : int =
  match value with RBLeaf -> 0 | RBNode (_, _, key, _) -> key

let[@refined.logic] rb_right (value : rb_tree) : rb_tree =
  match value with RBLeaf -> RBLeaf | RBNode (_, _, _, right) -> right

let[@refined.logic] case_invariant (case : rb_case) : int =
  match case with RBCase (invariant, _, _, _) -> invariant

let[@refined.logic] case_color (case : rb_case) : bool =
  match case with RBCase (_, color, _, _) -> color

let[@refined.logic] case_height (case : rb_case) : int =
  match case with RBCase (_, _, height, _) -> height

let[@refined.logic] case_tree (case : rb_case) : rb_tree =
  match case with RBCase (_, _, _, value) -> value

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.predicate] rb_target (v : rb_tree) (color : bool) (h : int) : bool
    =
  h >= 0 && rb_wellformed v h && root_allowed v color h

[@@@refined.axiom
{
  name = "black_zero";
  quantifiers = [ ("forall", "v", "rb_tree") ];
  body = "implies (rb_target v true 0) (v = RBLeaf)";
}]

[@@@refined.axiom
{
  name = "red_zero";
  quantifiers = [ ("forall", "v", "rb_tree") ];
  body =
    "implies (rb_target v false 0) (v = RBLeaf || v = RBNode (true, RBLeaf, \
     rb_key v, RBLeaf))";
}]

[@@@refined.axiom
{
  name = "black_positive";
  quantifiers = [ ("forall", "v", "rb_tree"); ("forall", "h", "int") ];
  body =
    "implies (h > 0 && rb_target v true h) (v = RBNode (false, rb_left v, \
     rb_key v, rb_right v) && rb_target (rb_left v) false (h - 1) && rb_target \
     (rb_right v) false (h - 1))";
}]

[@@@refined.axiom
{
  name = "red_positive";
  quantifiers = [ ("forall", "v", "rb_tree"); ("forall", "h", "int") ];
  body =
    "implies (h > 0 && rb_target v false h) ((v = RBNode (false, rb_left v, \
     rb_key v, rb_right v) && rb_target (rb_left v) false (h - 1) && rb_target \
     (rb_right v) false (h - 1)) || (v = RBNode (true, rb_left v, rb_key v, \
     rb_right v) && rb_target (rb_left v) true h && rb_target (rb_right v) \
     true h))";
}]

let[@refined.coverage
     {
       type_ =
         "invariant:{invariant:int | invariant >= 0} -> color:bool -> \
          height:{height:int | height >= 0 && ((color && invariant = 2 * \
          height) || (not color && invariant = 2 * height + 1))} -> {r:rb_tree \
          | rb_target r color height}";
       universals = [ "invariant"; "color"; "height" ];
       witness_relation = "true";
     }]
   [@refined.measure "invariant"] rec red_black_tree_port (invariant : int)
    (color : bool) (height : int) : rb_tree =
  if invariant < 0 then raise Reject
  else if height = 0 then
    if color then RBLeaf
    else if bool_gen () then RBLeaf
    else RBNode (true, RBLeaf, int_gen (), RBLeaf)
  else
    let h = height - 1 in
    let key = int_gen () in
    if color then
      let left = red_black_tree_port (invariant - 1) false h in
      let right = red_black_tree_port (invariant - 1) false h in
      RBNode (false, left, key, right)
    else if bool_gen () then
      let left = red_black_tree_port (invariant - 1) true height in
      let right = red_black_tree_port (invariant - 1) true height in
      RBNode (true, left, key, right)
    else
      let left = red_black_tree_port (invariant - 2) false h in
      let right = red_black_tree_port (invariant - 2) false h in
      RBNode (false, left, key, right)

let runtime_examples (_unit : unit) =
  rb_target (red_black_tree_port 6 true 3) true 3
  && rb_target (red_black_tree_port 7 false 3) false 3
  && rb_target (red_black_tree_port 1 false 0) false 0
