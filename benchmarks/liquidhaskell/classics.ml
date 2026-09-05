(* SPDX-License-Identifier: BSD-3-Clause
   Algorithm ports from the pinned LiquidHaskell tutorial. PORTS.md maps
   each chapter to its operations, properties and representation changes. *)
exception Empty_input

type ilist = Nil | Cons of int * ilist

let[@refined.logic] rec length (v : ilist) : int =
  match v with Nil -> 0 | Cons (_, t) -> 1 + length t

let[@refined.predicate] rec member (x : int) (v : ilist) : bool =
  match v with Nil -> false | Cons (h, t) -> x = h || member x t

let[@refined.predicate] rec all_ge (v : ilist) (lo : int) : bool =
  match v with Nil -> true | Cons (h, t) -> h >= lo && all_ge t lo

let[@refined.predicate] rec ordered (v : ilist) (lo : int) : bool =
  match v with Nil -> true | Cons (h, t) -> h >= lo && ordered t h

[@@@refined.axiom
{ name = "length_nil"; quantifiers = []; body = "length Nil = 0" }]

[@@@refined.axiom
{
  name = "length_cons";
  quantifiers = [ ("forall", "h", "int"); ("forall", "t", "ilist") ];
  body = "length (Cons (h,t)) = 1 + length t && length t >= 0";
}]

[@@@refined.axiom
{
  name = "length_nonnegative";
  quantifiers = [ ("forall", "v", "ilist") ];
  body = "length v >= 0";
}]

[@@@refined.axiom
{
  name = "member_nil";
  quantifiers = [ ("forall", "x", "int") ];
  body = "not (member x Nil)";
}]

[@@@refined.axiom
{
  name = "member_cons";
  quantifiers =
    [ ("forall", "x", "int"); ("forall", "h", "int"); ("forall", "t", "ilist") ];
  body = "member x (Cons (h,t)) = (x = h || member x t)";
}]

[@@@refined.axiom
{
  name = "ge_nil";
  quantifiers = [ ("forall", "lo", "int") ];
  body = "all_ge Nil lo";
}]

[@@@refined.axiom
{
  name = "ge_cons";
  quantifiers =
    [
      ("forall", "h", "int"); ("forall", "t", "ilist"); ("forall", "lo", "int");
    ];
  body = "all_ge (Cons (h,t)) lo = (h >= lo && all_ge t lo)";
}]

[@@@refined.axiom
{
  name = "ordered_nil";
  quantifiers = [ ("forall", "lo", "int") ];
  body = "ordered Nil lo";
}]

[@@@refined.axiom
{
  name = "ordered_cons";
  quantifiers =
    [
      ("forall", "h", "int"); ("forall", "t", "ilist"); ("forall", "lo", "int");
    ];
  body = "ordered (Cons (h,t)) lo = (h >= lo && ordered t h)";
}]

[@@@refined.axiom
{
  name = "ordered_weaken";
  quantifiers =
    [
      ("forall", "v", "ilist"); ("forall", "lo", "int"); ("forall", "hi", "int");
    ];
  body = "implies (lo <= hi && ordered v hi) (ordered v lo)";
}]

let[@refined.over { type_ = "p:bool -> q:bool -> {r:bool | r = (not p || q)}" }] logic_implication
    (p : bool) (q : bool) : bool =
  (not p) || q

let[@refined.over { type_ = "p:bool -> {r:bool | r}" }] excluded_middle
    (p : bool) : bool =
  p || not p

let[@refined.over { type_ = "p:bool -> {r:bool | not r}" }] contradiction
    (p : bool) : bool =
  p && not p

let[@refined.over { type_ = "p:bool -> q:bool -> {r:bool | r}" }] de_morgan
    (p : bool) (q : bool) : bool =
  (not (p && q)) = ((not p) || not q)

let[@refined.over { type_ = "p:bool -> q:bool -> z:bool -> {r:bool | r}" }] implication_transitive
    (p : bool) (q : bool) (z : bool) : bool =
  (not (((not p) || q) && ((not q) || z))) || (not p) || z

let[@refined.over { type_ = "x:int -> y:int -> z:int -> {r:bool | r}" }] arithmetic_transitive
    (x : int) (y : int) (z : int) : bool =
  (not (x < y && y < z)) || x < z

let[@refined.over
     { type_ = "x:int -> {r:int | r >= 0 && (r = x || r = 0 - x)}" }] basic_absolute
    (x : int) : int =
  if x >= 0 then x else 0 - x

let[@refined.over { type_ = "x:int -> y:{y:int | y <> 0} -> {r:int | true}" }] divide
    (x : int) (y : int) : int =
  x / y

let[@refined.over { type_ = "x:int -> bound:int -> {r:int | true}" }] truncate
    (x : int) (bound : int) : int =
  let a = basic_absolute x in
  let b = basic_absolute bound in
  if a <= b then x else b * divide x a

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> v:{v:ilist | length v = n} -> index:{index:int \
          | 0 <= index && index < n} -> {r:int | true}";
     }]
   [@refined.measure "n"] rec vector_get (n : int) (v : ilist) (index : int) :
    int =
  match v with
  | Nil -> 0
  | Cons (h, t) -> if index = 0 then h else vector_get (n - 1) t (index - 1)

let[@refined.over
     {
       type_ =
         "remaining:{remaining:int | remaining >= 0} -> index:{index:int | \
          index >= 0} -> limit:{limit:int | limit = index + remaining} -> \
          initial:int -> step:(j:{j:int | index <= j && j < limit} -> acc:int \
          -> int) -> {r:int | true}";
     }]
   [@refined.measure "remaining"] rec loop (remaining : int) (index : int)
    (limit : int) (initial : int) (step : int -> int -> int) : int =
  if index < limit then
    let next = step index initial in
    loop (remaining - 1) (index + 1) limit next step
  else initial

let[@refined.over
     {
       type_ =
         "size:{size:int | size >= 0} -> v:{v:ilist | length v = size} -> \
          {r:int | true}";
     }] vector_sum (size : int) (v : ilist) : int =
  loop size 0 size 0 (fun index acc -> acc + vector_get size v index)

let[@refined.over
     {
       type_ =
         "remaining:{remaining:int | remaining >= 0} -> index:{index:int | \
          index >= 0} -> size:{size:int | size = index + remaining} -> \
          v:{v:ilist | length v = size} -> {r:int | r >= 0}";
     }]
   [@refined.measure "remaining"] rec absolute_sum (remaining : int)
    (index : int) (size : int) (v : ilist) : int =
  if remaining = 0 then 0
  else
    let x = basic_absolute (vector_get size v index) in
    x + absolute_sum (remaining - 1) (index + 1) size v

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> lower:int -> x:{x:int | x >= lower} -> \
          xs:{xs:ilist | length xs = n && ordered xs lower} -> {r:ilist | \
          length r = n + 1 && ordered r lower}";
     }]
   [@refined.measure "n"] rec insert (n : int) (lower : int) (x : int)
    (xs : ilist) : ilist =
  match xs with
  | Nil -> Cons (x, Nil)
  | Cons (h, t) ->
      if x <= h then Cons (x, xs) else Cons (h, insert (n - 1) h x t)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> lower:int -> xs:{xs:ilist | length xs = n && \
          all_ge xs lower} -> {r:ilist | length r = n && ordered r lower}";
     }]
   [@refined.measure "n"] rec insertion_sort (n : int) (lower : int)
    (xs : ilist) : ilist =
  match xs with
  | Nil -> Nil
  | Cons (h, t) -> insert (n - 1) lower h (insertion_sort (n - 1) lower t)

let[@refined.over { type_ = "xs:{xs:ilist | length xs > 0} -> {r:int | true}" }] nonempty_head
    (xs : ilist) : int =
  match xs with Nil -> raise Empty_input | Cons (h, _t) -> h

let[@refined.over
     {
       type_ =
         "xs:{xs:ilist | length xs > 0} -> {r:ilist | length r = length xs - 1}";
     }] nonempty_tail (xs : ilist) : ilist =
  match xs with Nil -> raise Empty_input | Cons (_h, t) -> t

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> xs:{xs:ilist | length xs = n} -> {r:int | r = \
          n}";
     }]
   [@refined.measure "n"] rec list_size (n : int) (xs : ilist) : int =
  match xs with Nil -> 0 | Cons (_, t) -> 1 + list_size (n - 1) t

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> xs:{xs:ilist | length xs = n} -> {r:int | true}";
     }]
   [@refined.measure "n"] rec list_sum (n : int) (xs : ilist) : int =
  match xs with Nil -> 0 | Cons (h, t) -> h + list_sum (n - 1) t

let[@refined.over
     {
       type_ =
         "n:{n:int | n > 0} -> xs:{xs:ilist | length xs = n} -> {r:int | true}";
     }] average (n : int) (xs : ilist) : int =
  divide (list_sum n xs) (list_size n xs)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> xs:{xs:ilist | length xs = n} -> ys:ilist -> \
          {r:ilist | length r = n + length ys}";
     }]
   [@refined.measure "n"] rec append (n : int) (xs : ilist) (ys : ilist) : ilist
    =
  match xs with Nil -> ys | Cons (h, t) -> Cons (h, append (n - 1) t ys)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> xs:{xs:ilist | length xs = n} -> acc:ilist -> \
          {r:ilist | length r = n + length acc}";
     }]
   [@refined.measure "n"] rec reverse_acc (n : int) (xs : ilist) (acc : ilist) :
    ilist =
  match xs with
  | Nil -> acc
  | Cons (h, t) -> reverse_acc (n - 1) t (Cons (h, acc))

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> xs:{xs:ilist | length xs = n} -> {r:ilist | \
          length r = n}";
     }] reverse (n : int) (xs : ilist) : ilist =
  reverse_acc n xs Nil

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> f:(x:int -> int) -> xs:{xs:ilist | length xs = \
          n} -> {r:ilist | length r = n}";
     }]
   [@refined.measure "n"] rec map (n : int) (f : int -> int) (xs : ilist) :
    ilist =
  match xs with Nil -> Nil | Cons (h, t) -> Cons (f h, map (n - 1) f t)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> f:(x:int -> y:int -> int) -> xs:{xs:ilist | \
          length xs = n} -> ys:{ys:ilist | length ys = n} -> {r:ilist | length \
          r = n}";
     }]
   [@refined.measure "n"] rec zip_with (n : int) (f : int -> int -> int)
    (xs : ilist) (ys : ilist) : ilist =
  match xs with
  | Nil -> Nil
  | Cons (x, xt) -> (
      match ys with
      | Nil -> raise Empty_input
      | Cons (y, yt) -> Cons (f x y, zip_with (n - 1) f xt yt))

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> query:int -> xs:{xs:ilist | length xs = n} -> \
          {r:ilist | member query r = member query xs && length r <= n}";
     }]
   [@refined.measure "n"] rec nub (n : int) (query : int) (xs : ilist) : ilist =
  match xs with
  | Nil -> Nil
  | Cons (h, t) ->
      let rest = nub (n - 1) query t in
      if member h t then rest else Cons (h, rest)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> query:int -> xs:{xs:ilist | length xs = n} -> \
          ys:ilist -> {r:ilist | member query r = (member query xs || member \
          query ys)}";
     }]
   [@refined.measure "n"] rec append_set (n : int) (query : int) (xs : ilist)
    (ys : ilist) : ilist =
  match xs with
  | Nil -> ys
  | Cons (h, t) -> Cons (h, append_set (n - 1) query t ys)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> xs:{xs:ilist | length xs = n} -> \
          index:{index:int | 0 <= index && index < n} -> value:int -> {r:ilist \
          | length r = n}";
     }]
   [@refined.measure "n"] rec set_at (n : int) (xs : ilist) (index : int)
    (value : int) : ilist =
  match xs with
  | Nil -> raise Empty_input
  | Cons (h, t) ->
      if index = 0 then Cons (value, t)
      else Cons (h, set_at (n - 1) t (index - 1) value)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> v:{v:ilist | length v = n} -> index:{index:int \
          | 0 <= index && index < n} -> {r:int | true}";
     }]
   [@refined.measure "n"] rec peek_at (n : int) (v : ilist) (index : int) : int
    =
  match v with
  | Nil -> raise Empty_input
  | Cons (h, t) -> if index = 0 then h else peek_at (n - 1) t (index - 1)

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> buffer:ilist ref -> offset:{offset:int | 0 <= \
          offset && offset < n} -> byte:int -> {r:unit | true}";
       requires_state = [ ("buffer", "length value = n") ];
       state = [ ("buffer", "length value = n") ];
     }] poke (n : int) (buffer : ilist ref) (offset : int) (byte : int) : unit =
  buffer := set_at n !buffer offset byte

let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> buffer:ilist ref -> offset:{offset:int | 0 <= \
          offset && offset < n} -> {r:int | true}";
       requires_state = [ ("buffer", "length value = n") ];
     }] peek (n : int) (buffer : ilist ref) (offset : int) : int =
  peek_at n !buffer offset

let[@refined.over
     {
       type_ =
         "remaining:{remaining:int | remaining >= 0} -> offset:{offset:int | \
          offset >= 0} -> n:{n:int | n = offset + remaining} -> buffer:ilist \
          ref -> {r:unit | true}";
       requires_state = [ ("buffer", "length value = n") ];
       state = [ ("buffer", "length value = n") ];
     }]
   [@refined.measure "remaining"] rec zero_fill (remaining : int) (offset : int)
    (n : int) (buffer : ilist ref) : unit =
  if remaining = 0 then ()
  else (
    poke n buffer offset 0;
    zero_fill (remaining - 1) (offset + 1) n buffer)

let runtime_examples (_u : unit) =
  let xs = Cons (3, Cons (1, Cons (2, Nil))) in
  let sorted = Cons (1, Cons (2, Cons (3, Nil))) in
  let buffer = ref xs in
  poke 3 buffer 1 9;
  let changed = peek 3 buffer 1 = 9 in
  zero_fill 2 1 3 buffer;
  changed
  && !buffer = Cons (3, Cons (0, Cons (0, Nil)))
  && insertion_sort 3 0 xs = sorted
  && reverse 3 xs = Cons (2, Cons (1, Cons (3, Nil)))
  && map 3 (fun x -> x + 1) xs = Cons (4, Cons (2, Cons (3, Nil)))
  && zip_with 3 (fun x y -> x + y) xs sorted = Cons (4, Cons (3, Cons (5, Nil)))
  && nub 4 3 (Cons (3, xs)) = xs
  && append 3 xs sorted = Cons (3, Cons (1, Cons (2, sorted)))
  && average 3 xs = 2
  && nonempty_head xs = 3
  && nonempty_tail xs = Cons (1, Cons (2, Nil))
  && vector_sum 3 xs = 6
  && absolute_sum 3 0 3 (Cons (-3, Cons (1, Cons (-2, Nil)))) = 6
