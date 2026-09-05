(* SPDX-License-Identifier: BSD-3-Clause
   Okasaki queue operations from tutorial chapter 09. The port is strict OCaml;
   it verifies sizes, balance, and safe removal, not Haskell's lazy cost bound.
   The integer argument to rotate exposes the original front-size measure. *)
type ilist = Nil | Cons of int * ilist
type queue = Q of ilist * ilist
type removed = Removed of int * queue

let rec count value =
  match value with Nil -> 0 | Cons (_, tail) -> 1 + count tail

let[@refined.logic] length (value : ilist) : int = count value

let[@refined.logic] qsize (value : queue) : int =
  match value with Q (front, back) -> count front + count back

let[@refined.predicate] balanced (value : queue) : bool =
  match value with Q (front, back) -> count back <= count front

let[@refined.logic] rest (value : removed) : queue =
  match value with Removed (_, queue) -> queue

[@@@refined.axiom
{ name = "length_nil"; quantifiers = []; body = "length Nil = 0" }]

[@@@refined.axiom
{
  name = "length_cons";
  quantifiers = [ ("forall", "head", "int"); ("forall", "tail", "ilist") ];
  body = "length (Cons (head, tail)) = 1 + length tail";
}]

[@@@refined.axiom
{
  name = "length_nonnegative";
  quantifiers = [ ("forall", "value", "ilist") ];
  body = "length value >= 0";
}]

[@@@refined.axiom
{
  name = "queue_size";
  quantifiers = [ ("forall", "front", "ilist"); ("forall", "back", "ilist") ];
  body = "qsize (Q (front, back)) = length front + length back";
}]

[@@@refined.axiom
{
  name = "queue_balance";
  quantifiers = [ ("forall", "front", "ilist"); ("forall", "back", "ilist") ];
  body = "balanced (Q (front, back)) = (length back <= length front)";
}]

[@@@refined.axiom
{
  name = "removed_rest";
  quantifiers = [ ("forall", "head", "int"); ("forall", "queue", "queue") ];
  body = "rest (Removed (head, queue)) = queue";
}]

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> front:{v:ilist | length v = n} -> \
          back:{v:ilist | length v = n + 1} -> acc:ilist -> {r:ilist | length \
          r = length front + length back + length acc}";
     }]
   [@refined.measure "n"] rec rotate (n : int) (front : ilist) (back : ilist)
    (acc : ilist) : ilist =
  match front with
  | Nil -> ( match back with Nil -> Nil | Cons (head, _) -> Cons (head, acc))
  | Cons (head, tail) -> (
      match back with
      | Nil -> Nil
      | Cons (last, remaining) ->
          Cons (head, rotate (n - 1) tail remaining (Cons (last, acc))))

let[@refined.over
     {
       type_ =
         "front:ilist -> back:{v:ilist | length v <= length front + 1} -> \
          {r:queue | balanced r && qsize r = length front + length back}";
     }] makeq (front : ilist) (back : ilist) : queue =
  if length back <= length front then Q (front, back)
  else Q (rotate (length front) front back Nil, Nil)

let[@refined.over
     { type_ = "_unit:unit -> {r:queue | balanced r && qsize r = 0}" }] empty
    (_unit : unit) : queue =
  Q (Nil, Nil)

let[@refined.over
     {
       type_ =
         "element:int -> queue:{v:queue | balanced v} -> {r:queue | balanced r \
          && qsize r = qsize queue + 1}";
     }] insert (element : int) (queue : queue) : queue =
  match queue with Q (front, back) -> makeq front (Cons (element, back))

let[@refined.over
     {
       type_ =
         "queue:{v:queue | balanced v && qsize v > 0} -> {r:removed | balanced \
          (rest r) && qsize (rest r) = qsize queue - 1}";
     }] remove (queue : queue) : removed =
  match queue with
  | Q (front, back) -> (
      match front with
      | Nil -> Removed (0, Q (Nil, Nil))
      | Cons (head, tail) -> Removed (head, makeq tail back))

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> element:int -> {r:queue | balanced r && qsize \
          r = n}";
     }]
   [@refined.measure "n"] rec replicate (n : int) (element : int) : queue =
  if n = 0 then empty () else insert element (replicate (n - 1) element)

let[@refined.over
     { type_ = "_unit:unit -> {r:queue | balanced r && qsize r = 3}" }] example
    (_unit : unit) : queue =
  insert 3 (insert 2 (insert 1 (empty ())))

let runtime_examples (_unit : unit) : bool =
  let q = example () in
  let (Removed (a, q)) = remove q in
  let (Removed (b, q)) = remove q in
  let (Removed (c, q)) = remove q in
  let (Removed (first, q2)) = remove (insert 2 (insert 1 (empty ()))) in
  let (Removed (second, q2)) = remove q2 in
  first = 1 && second = 2
  && qsize q2 = 0
  && balanced q2 && a = 1 && b = 2 && c = 3
  && qsize q = 0
  && balanced q
  && qsize (replicate 8 42) = 8
  && balanced (replicate 8 42)
