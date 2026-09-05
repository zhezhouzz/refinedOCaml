(* SPDX-License-Identifier: BSD-3-Clause
   Chapter 10: ordered finite maps, membership and total lookup on present keys. *)
exception Missing_key

type map = Tip | Node of int * int * map * map

let[@refined.logic] rec size (m : map) : int =
  match m with Tip -> 0 | Node (_, _, l, r) -> 1 + size l + size r

let[@refined.predicate] rec ordered (m : map) (lo : int) (hi : int) : bool =
  match m with
  | Tip -> true
  | Node (k, _, l, r) -> lo < k && k < hi && ordered l lo k && ordered r k hi

let[@refined.predicate] rec has (m : map) (key : int) : bool =
  match m with
  | Tip -> false
  | Node (k, _, l, r) ->
      if key = k then true else if key < k then has l key else has r key

let[@refined.logic] rec value (m : map) (key : int) : int =
  match m with
  | Tip -> 0
  | Node (k, v, l, r) ->
      if key = k then v else if key < k then value l key else value r key

[@@@refined.axiom
{
  name = "empty";
  quantifiers =
    [ ("forall", "lo", "int"); ("forall", "hi", "int"); ("forall", "q", "int") ];
  body =
    "size Tip = 0 && ordered Tip lo hi && not (has Tip q) && value Tip q = 0";
}]

[@@@refined.axiom
{
  name = "node_size";
  quantifiers =
    [
      ("forall", "k", "int");
      ("forall", "v", "int");
      ("forall", "l", "map");
      ("forall", "r", "map");
    ];
  body =
    "size (Node (k,v,l,r)) = 1 + size l + size r && size l >= 0 && size r >= 0";
}]

[@@@refined.axiom
{
  name = "node_order";
  quantifiers =
    [
      ("forall", "k", "int");
      ("forall", "v", "int");
      ("forall", "l", "map");
      ("forall", "r", "map");
      ("forall", "lo", "int");
      ("forall", "hi", "int");
    ];
  body =
    "ordered (Node (k,v,l,r)) lo hi = (lo < k && k < hi && ordered l lo k && \
     ordered r k hi)";
}]

[@@@refined.axiom
{
  name = "node_has";
  quantifiers =
    [
      ("forall", "k", "int");
      ("forall", "v", "int");
      ("forall", "l", "map");
      ("forall", "r", "map");
      ("forall", "q", "int");
    ];
  body =
    "has (Node (k,v,l,r)) q = (q = k || (q < k && has l q) || (q > k && has r \
     q))";
}]

[@@@refined.axiom
{
  name = "node_value";
  quantifiers =
    [
      ("forall", "k", "int");
      ("forall", "v", "int");
      ("forall", "l", "map");
      ("forall", "r", "map");
      ("forall", "q", "int");
    ];
  body =
    "(q = k && value (Node (k,v,l,r)) q = v) || (q < k && value (Node \
     (k,v,l,r)) q = value l q) || (q > k && value (Node (k,v,l,r)) q = value r \
     q)";
}]

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> lower:int -> upper:int -> key:{key:int | lower \
          < key && key < upper} -> entry:int -> query:int -> m:{m:map | size m \
          = n && ordered m lower upper} -> {r:map | ordered r lower upper && n \
          <= size r && size r <= n + 1 && has r query = (query = key || has m \
          query) && ((query = key && value r query = entry) || (query <> key \
          && value r query = value m query))}";
     }]
   [@refined.measure "n"] rec set (n : int) (lower : int) (upper : int)
    (key : int) (entry : int) (query : int) (m : map) : map =
  match m with
  | Tip -> Node (key, entry, Tip, Tip)
  | Node (k, v, l, r) ->
      if key = k then Node (k, entry, l, r)
      else if key < k then Node (k, v, set (size l) lower k key entry query l, r)
      else Node (k, v, l, set (size r) k upper key entry query r)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> key:int -> m:{m:map | size m = n && has m key} \
          -> {r:int | r = value m key}";
     }]
   [@refined.measure "n"] rec get (n : int) (key : int) (m : map) : int =
  match m with
  | Tip -> raise Missing_key
  | Node (k, v, l, r) ->
      if key = k then v
      else if key < k then get (size l) key l
      else get (size r) key r

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> key:int -> m:{m:map | size m = n} -> {r:bool | \
          r = has m key}";
     }]
   [@refined.measure "n"] rec mem (n : int) (key : int) (m : map) : bool =
  match m with
  | Tip -> false
  | Node (k, _v, l, r) ->
      if key = k then true
      else if key < k then mem (size l) key l
      else mem (size r) key r

let runtime_examples (_u : unit) =
  let a = set 0 (-100) 100 4 40 4 Tip in
  let b = set 1 (-100) 100 2 20 4 a in
  let c = set 2 (-100) 100 7 70 4 b in
  let d = set 3 (-100) 100 4 41 4 c in
  ordered d (-100) 100
  && get 3 4 d = 41
  && get 3 2 d = 20
  && get 3 7 d = 70
  && (not (mem 3 5 d))
  && size d = 3
