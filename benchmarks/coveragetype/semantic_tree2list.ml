(* SPDX-License-Identifier: MIT
   Corrected preorder traversal. upstream_flatten retains the source defect. *)
type tree = Leaf | Node of int * tree * tree
type ilist = Nil | Cons of int * ilist

let[@refined.logic] rec tree_nodes (t : tree) : int =
  match t with Leaf -> 0 | Node (_, l, r) -> 1 + tree_nodes l + tree_nodes r

let[@refined.logic] rec list_length (l : ilist) : int =
  match l with Nil -> 0 | Cons (_, t) -> 1 + list_length t

let[@refined.logic] rec cat (a : ilist) (b : ilist) : ilist =
  match a with Nil -> b | Cons (h, t) -> Cons (h, cat t b)

let[@refined.logic] rec preorder (t : tree) : ilist =
  match t with
  | Leaf -> Nil
  | Node (x, l, r) -> Cons (x, cat (preorder l) (preorder r))

let[@refined.logic] rec spine (l : ilist) : tree =
  match l with Nil -> Leaf | Cons (h, t) -> Node (h, Leaf, spine t)

[@@@refined.axiom
{ name = "list_nil"; quantifiers = []; body = "list_length Nil = 0" }]

[@@@refined.axiom
{
  name = "list_cons";
  quantifiers = [ ("forall", "h", "int"); ("forall", "t", "ilist") ];
  body = "list_length (Cons (h,t)) = 1 + list_length t && list_length t >= 0";
}]

[@@@refined.axiom
{
  name = "tree_leaf";
  quantifiers = [];
  body = "tree_nodes Leaf = 0 && preorder Leaf = Nil";
}]

[@@@refined.axiom
{
  name = "tree_node";
  quantifiers =
    [ ("forall", "x", "int"); ("forall", "l", "tree"); ("forall", "r", "tree") ];
  body =
    "tree_nodes (Node (x,l,r)) = 1 + tree_nodes l + tree_nodes r && tree_nodes \
     l >= 0 && tree_nodes r >= 0 && preorder (Node (x,l,r)) = Cons (x,cat \
     (preorder l) (preorder r))";
}]

[@@@refined.axiom
{
  name = "cat_nil";
  quantifiers = [ ("forall", "b", "ilist") ];
  body = "cat Nil b = b";
}]

[@@@refined.axiom
{
  name = "cat_cons";
  quantifiers =
    [
      ("forall", "h", "int"); ("forall", "t", "ilist"); ("forall", "b", "ilist");
    ];
  body = "cat (Cons (h,t)) b = Cons (h,cat t b)";
}]

[@@@refined.axiom
{
  name = "spine_inverse";
  quantifiers = [ ("forall", "l", "ilist") ];
  body =
    "preorder (spine l) = l && tree_nodes (spine l) = list_length l && \
     list_length l >= 0";
}]

let[@refined.logic] first (l : ilist) : int =
  match l with Nil -> 0 | Cons (h, _) -> h

let[@refined.logic] rest (l : ilist) : ilist =
  match l with Nil -> Nil | Cons (_, t) -> t

[@@@refined.axiom
{ name = "spine_nil"; quantifiers = []; body = "spine Nil = Leaf" }]

[@@@refined.axiom
{
  name = "spine_cons";
  quantifiers = [ ("forall", "h", "int"); ("forall", "t", "ilist") ];
  body = "spine (Cons (h,t)) = Node (h,Leaf,spine t)";
}]

[@@@refined.axiom
{
  name = "list_elim";
  quantifiers = [ ("forall", "v", "ilist") ];
  body = "v = Nil || v = Cons (first v,rest v)";
}]

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> a:{a:ilist | list_length a = n} -> b:ilist -> \
          {r:ilist | r = cat a b && list_length r = n + list_length b}";
     }]
   [@refined.coverage
     {
       type_ =
         "n:{n:int | n >= 0} -> a:{a:ilist | list_length a = n} -> b:ilist -> \
          ilist";
       witnesses = [ ("n", "0"); ("a", "Nil"); ("b", "result") ];
     }]
   [@refined.measure "n"] rec append (n : int) (a : ilist) (b : ilist) : ilist =
  match a with Nil -> b | Cons (h, t) -> Cons (h, append (n - 1) t b)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> t:{t:tree | tree_nodes t = n} -> {r:ilist | \
          list_length r = n && r = preorder t}";
     }]
   [@refined.coverage
     {
       type_ = "n:{n:int | n >= 0} -> t:{t:tree | tree_nodes t = n} -> ilist";
       witnesses = [ ("n", "list_length result"); ("t", "spine result") ];
     }]
   [@refined.measure "n"] rec flatten (n : int) (t : tree) : ilist =
  match t with
  | Leaf -> Nil
  | Node (x, l, r) ->
      let left = flatten (tree_nodes l) l in
      let right = flatten (tree_nodes r) r in
      Cons (x, append (tree_nodes l) left right)

let rec upstream_flatten (n : int) (t : tree) : ilist =
  match t with
  | Leaf -> Nil
  | Node (x, _l, r) -> Cons (x, upstream_flatten (n - 1) r)

let[@refined.choose] tree_gen (_u : unit) : tree = Leaf

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:ilist | true}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] list_gen (unit_value : unit) : ilist =
  let t = tree_gen () in
  flatten (tree_nodes t) t

let runtime_examples (_u : unit) =
  let t = Node (1, Node (2, Leaf, Leaf), Node (3, Leaf, Leaf)) in
  flatten 3 t = Cons (1, Cons (2, Cons (3, Nil)))
  && list_length (upstream_flatten 3 t) = 2
  && list_gen () = Nil
