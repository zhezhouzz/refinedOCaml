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

[@@@refined.axiom
{ name = "nonred_leaf"; quantifiers = []; body = "nonred_root RBLeaf" }]

[@@@refined.axiom
{
  name = "nonred_black";
  quantifiers =
    [
      ("forall", "left", "rb_tree");
      ("forall", "key", "int");
      ("forall", "right", "rb_tree");
    ];
  body = "nonred_root (RBNode (false, left, key, right))";
}]

[@@@refined.axiom
{
  name = "nonred_elim";
  quantifiers = [ ("forall", "value", "rb_tree") ];
  body =
    "implies (nonred_root value) (value = RBLeaf || value = RBNode (false, \
     rb_left value, rb_key value, rb_right value))";
}]

[@@@refined.axiom
{ name = "rb_leaf"; quantifiers = []; body = "rb_wellformed RBLeaf 0" }]

[@@@refined.axiom
{
  name = "rb_red_intro";
  quantifiers =
    [
      ("forall", "height", "int");
      ("forall", "left", "rb_tree");
      ("forall", "key", "int");
      ("forall", "right", "rb_tree");
    ];
  body =
    "implies (height >= 0 && rb_wellformed left height && rb_wellformed right \
     height && nonred_root left && nonred_root right) (rb_wellformed (RBNode \
     (true, left, key, right)) height)";
}]

[@@@refined.axiom
{
  name = "rb_black_intro";
  quantifiers =
    [
      ("forall", "height", "int");
      ("forall", "left", "rb_tree");
      ("forall", "key", "int");
      ("forall", "right", "rb_tree");
    ];
  body =
    "implies (height > 0 && rb_wellformed left (height - 1) && rb_wellformed \
     right (height - 1)) (rb_wellformed (RBNode (false, left, key, right)) \
     height)";
}]

[@@@refined.axiom
{
  name = "rb_elim";
  quantifiers = [ ("forall", "value", "rb_tree"); ("forall", "height", "int") ];
  body =
    "implies (rb_wellformed value height) ((height = 0 && value = RBLeaf) || \
     (height >= 0 && value = RBNode (true, rb_left value, rb_key value, \
     rb_right value) && rb_wellformed (rb_left value) height && rb_wellformed \
     (rb_right value) height && nonred_root (rb_left value) && nonred_root \
     (rb_right value)) || (height > 0 && value = RBNode (false, rb_left value, \
     rb_key value, rb_right value) && rb_wellformed (rb_left value) (height - \
     1) && rb_wellformed (rb_right value) (height - 1)))";
}]

[@@@refined.axiom
{
  name = "rb_case_intro";
  quantifiers =
    [
      ("forall", "invariant", "int");
      ("forall", "color", "bool");
      ("forall", "height", "int");
      ("forall", "value", "rb_tree");
    ];
  body =
    "implies (invariant >= 0 && height >= 0 && ((color && 2 * height = \
     invariant) || (not color && 2 * height + 1 = invariant)) && rb_wellformed \
     value height && root_allowed value color height) (valid_rb_case (RBCase \
     (invariant, color, height, value)))";
}]

[@@@refined.axiom
{
  name = "rb_case_elim";
  quantifiers = [ ("forall", "case", "rb_case") ];
  body =
    "implies (valid_rb_case case) (case = RBCase (case_invariant case, \
     case_color case, case_height case, case_tree case) && case_invariant case \
     >= 0 && case_height case >= 0 && ((case_color case && 2 * case_height \
     case = case_invariant case) || (not (case_color case) && 2 * case_height \
     case + 1 = case_invariant case)) && rb_wellformed (case_tree case) \
     (case_height case) && root_allowed (case_tree case) (case_color case) \
     (case_height case))";
}]

let[@refined.choose] choose_tree (left : rb_tree) (_right : rb_tree) : rb_tree =
  left

let[@refined.coverage
     {
       type_ =
         "invariant:{invariant:int | invariant >= 0} -> color:bool -> \
          height:{height:int | height >= 0} -> key:int -> left:rb_tree -> \
          right:rb_tree -> {result:rb_case | valid_rb_case result}";
       witness_relation =
         "result = RBCase (invariant, color, height, case_tree result) && \
          ((color && 2 * height = invariant) || (not color && 2 * height + 1 = \
          invariant)) && root_allowed (case_tree result) color height && \
          ((height = 0 && case_tree result = RBLeaf) || (height >= 0 && \
          case_tree result = RBNode (true, left, key, right) && rb_wellformed \
          left height && rb_wellformed right height && nonred_root left && \
          nonred_root right) || (height > 0 && case_tree result = RBNode \
          (false, left, key, right) && rb_wellformed left (height - 1) && \
          rb_wellformed right (height - 1)))";
     }] red_black_tree_port (invariant : int) (color : bool) (height : int)
    (key : int) (left : rb_tree) (right : rb_tree) : rb_case =
  let red = RBNode (true, left, key, right) in
  let black = RBNode (false, left, key, right) in
  RBCase (invariant, color, height, choose_tree RBLeaf (choose_tree red black))

let runtime_examples (_unit : unit) =
  let red_leaf = RBNode (true, RBLeaf, 1, RBLeaf) in
  let black_root = RBNode (false, red_leaf, 2, red_leaf) in
  let red_red = RBNode (true, red_leaf, 2, RBLeaf) in
  valid_rb_case (RBCase (3, false, 1, black_root))
  && valid_rb_case (RBCase (0, true, 0, RBLeaf))
  && (not (valid_rb_case (RBCase (2, false, 1, black_root))))
  && not (valid_rb_case (RBCase (1, false, 0, red_red)))
