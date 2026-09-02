(* SPDX-License-Identifier: BSD-3-Clause
   Original OCaml adaptations of the classic examples at the pinned
   LiquidHaskell tutorial revision recorded in ../manifest.tsv. *)

type 'a box = Box of 'a
type tree = Leaf | Node of int * tree * tree
type assoc = Empty | Bind of int * int * assoc

let[@refined.over { type_ = "p:bool -> q:bool -> {v:bool | v = (not p || q)}" }] logic_implication
    (p : bool) (q : bool) : bool =
  (not p) || q

let[@refined.over { type_ = "x:int -> {v:int | v >= 0}" }] basic_absolute
    (x : int) : int =
  if x >= 0 then x else 0 - x

let[@refined.over { type_ = "x:'a -> {v:'a | v = x}" }] polymorphic_identity
    (x : 'a) : 'a =
  x

let[@refined.over { type_ = "x:int -> {v:int box | v = Box x}" }] datatype_box
    (x : int) : int box =
  Box x

let[@refined.over { type_ = "flag:bool -> {v:bool | v = not flag}" }] boolean_measure
    (flag : bool) : bool =
  not flag

let[@refined.over { type_ = "n:{n:int | n >= 0} -> {v:int | v = 0}" }]
   [@refined.measure "n"] rec integer_measure (n : int) : int =
  if n = 0 then 0 else integer_measure (n - 1)

let[@refined.over { type_ = "x:int -> {v:int | v = x}" }] set_singleton
    (x : int) : int =
  x

let[@refined.over
     { type_ = "front:int list -> back:int list -> int list * int list" }] lazy_queue
    (front : int list) (back : int list) : int list * int list =
  (front, back)

let[@refined.over
     {
       type_ =
         "key:int -> value:int -> tail:assoc -> {v:assoc | v = Bind (key, \
          value, tail)}";
     }] associative_map (key : int) (value : int) (tail : assoc) : assoc =
  Bind (key, value, tail)

let[@refined.over
     {
       type_ = "cell:int ref -> {v:int | v >= 0}";
       requires_state = [ ("cell", "value >= 0") ];
     }] pointer_read (cell : int ref) : int =
  !cell

let[@refined.over { type_ = "x:int -> {v:tree | v = Node (x, Leaf, Leaf)}" }] avl_singleton
    (x : int) : tree =
  Node (x, Leaf, Leaf)
