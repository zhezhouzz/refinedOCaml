(* SPDX-License-Identifier: BSD-3-Clause
   Chapter 12: cached heights, ordered AVL trees, single/double rotations,
   and insertion. Explicit interval endpoints replace the tutorial's abstract
   ordering refinements; n exposes the tree-height termination measure. *)
type tree = Leaf | Node of int * int * tree * tree

let[@refined.logic] height (value : tree) : int =
  match value with Leaf -> 0 | Node (_, cached, _, _) -> cached

let[@refined.logic] maximum (left : int) (right : int) : int =
  if left >= right then left else right

let rec valid (value : tree) (lower : int) (upper : int) : bool =
  match value with
  | Leaf -> true
  | Node (key, cached, left, right) ->
      lower < key && key < upper && valid left lower key
      && valid right key upper
      && height left <= height right + 1
      && height right <= height left + 1
      && cached = 1 + maximum (height left) (height right)

let[@refined.predicate] avl (value : tree) (lower : int) (upper : int) : bool =
  valid value lower upper

[@@@refined.axiom
{
  name = "maximum_definition";
  quantifiers = [ ("forall", "left", "int"); ("forall", "right", "int") ];
  body =
    "(left >= right && maximum left right = left) || (left < right && maximum \
     left right = right)";
}]

[@@@refined.axiom
{ name = "height_leaf"; quantifiers = []; body = "height Leaf = 0" }]

[@@@refined.axiom
{
  name = "height_node";
  quantifiers =
    [
      ("forall", "key", "int");
      ("forall", "cached", "int");
      ("forall", "left", "tree");
      ("forall", "right", "tree");
    ];
  body = "height (Node (key, cached, left, right)) = cached";
}]

[@@@refined.axiom
{
  name = "avl_leaf";
  quantifiers = [ ("forall", "lower", "int"); ("forall", "upper", "int") ];
  body = "avl Leaf lower upper";
}]

[@@@refined.axiom
{
  name = "avl_nonnegative";
  quantifiers =
    [
      ("forall", "value", "tree");
      ("forall", "lower", "int");
      ("forall", "upper", "int");
    ];
  body = "implies (avl value lower upper) (height value >= 0)";
}]

[@@@refined.axiom
{
  name = "avl_node";
  quantifiers =
    [
      ("forall", "key", "int");
      ("forall", "cached", "int");
      ("forall", "left", "tree");
      ("forall", "right", "tree");
      ("forall", "lower", "int");
      ("forall", "upper", "int");
    ];
  body =
    "avl (Node (key, cached, left, right)) lower upper = (lower < key && key < \
     upper && avl left lower key && avl right key upper && height left <= \
     height right + 1 && height right <= height left + 1 && cached = 1 + \
     maximum (height left) (height right))";
}]

let[@refined.over
     {
       type_ =
         "lower:int -> upper:int -> key:{k:int | lower < k && k < upper} -> \
          left:{t:tree | avl t lower key} -> right:{t:tree | avl t key upper \
          && height left <= height t + 1 && height t <= height left + 1} -> \
          {r:tree | avl r lower upper && height r = 1 + maximum (height left) \
          (height right)}";
     }] node (lower : int) (upper : int) (key : int) (left : tree)
    (right : tree) : tree =
  Node (key, 1 + maximum (height left) (height right), left, right)

let[@refined.over
     {
       type_ =
         "lower:int -> upper:int -> key:{k:int | lower < k && k < upper} -> \
          left:{t:tree | avl t lower key} -> right:{t:tree | avl t key upper \
          && height left <= height t + 2 && height t <= height left + 2} -> \
          {r:tree | avl r lower upper && maximum (height left) (height right) \
          <= height r && height r <= 1 + maximum (height left) (height right) \
          && implies (height left <= height right + 1 && height right <= \
          height left + 1) (height r = 1 + maximum (height left) (height \
          right))}";
     }] balance (lower : int) (upper : int) (key : int) (left : tree)
    (right : tree) : tree =
  if height left > height right + 1 then
    match left with
    | Leaf -> Leaf
    | Node (lk, _, ll, lr) -> (
        if height ll >= height lr then
          node lower upper lk ll (node lk upper key lr right)
        else
          match lr with
          | Leaf -> Leaf
          | Node (mk, _, ml, mr) ->
              node lower upper mk (node lower mk lk ll ml)
                (node mk upper key mr right))
  else if height right > height left + 1 then
    match right with
    | Leaf -> Leaf
    | Node (rk, _, rl, rr) -> (
        if height rr >= height rl then
          node lower upper rk (node lower rk key left rl) rr
        else
          match rl with
          | Leaf -> Leaf
          | Node (mk, _, ml, mr) ->
              node lower upper mk
                (node lower mk key left ml)
                (node mk upper rk mr rr))
  else node lower upper key left right

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> lower:int -> upper:int -> element:{x:int | \
          lower < x && x < upper} -> value:{t:tree | avl t lower upper && \
          height t = n} -> {r:tree | avl r lower upper && n <= height r && \
          height r <= n + 1}";
     }]
   [@refined.measure "n"] rec insert (n : int) (lower : int) (upper : int)
    (element : int) (value : tree) : tree =
  match value with
  | Leaf -> node lower upper element Leaf Leaf
  | Node (key, _, left, right) ->
      if element < key then
        balance lower upper key
          (insert (height left) lower key element left)
          right
      else if key < element then
        balance lower upper key left
          (insert (height right) key upper element right)
      else value

let rec elements value =
  match value with
  | Leaf -> []
  | Node (key, _, left, right) -> elements left @ (key :: elements right)

let runtime_examples (_unit : unit) : bool =
  let build keys =
    List.fold_left
      (fun tree key -> insert (height tree) (-100) 100 key tree)
      Leaf keys
  in
  List.for_all
    (fun keys ->
      let tree = build keys in
      valid tree (-100) 100 && elements tree = List.sort_uniq compare keys)
    [
      [ 3; 2; 1 ];
      [ 3; 1; 2 ];
      [ 1; 2; 3 ];
      [ 1; 3; 2 ];
      [ 7; 3; 9; 2; 5; 8; 10; 4; 6; 1; 5 ];
    ]
