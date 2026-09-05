(* SPDX-License-Identifier: MIT
   Algorithm port at the revision in ../manifest.tsv. *)
type text = End | Byte of int * text
type rational = Rational of int * int
type rationals = No_rationals | More_rationals of rational * rationals
type priority = High | Medium | Low of rationals
type operation = Operation of int * text

let[@refined.logic] rec text_length (v : text) : int =
  match v with End -> 0 | Byte (_, t) -> 1 + text_length t

let[@refined.logic] text_head (v : text) : int =
  match v with End -> 0 | Byte (h, _) -> h

let[@refined.logic] text_tail (v : text) : text =
  match v with End -> End | Byte (_, t) -> t

let[@refined.predicate] rec bytes (v : text) : bool =
  match v with End -> true | Byte (h, t) -> 0 <= h && h <= 255 && bytes t

[@@@refined.axiom
{
  name = "text_elim";
  quantifiers = [ ("forall", "v", "text") ];
  body =
    "implies (bytes v) ((v = End && text_length v = 0) || (text_length v > 0 \
     && v = Byte (text_head v, text_tail v) && 0 <= text_head v && text_head v \
     <= 255 && bytes (text_tail v) && text_length (text_tail v) = text_length \
     v - 1))";
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
         "size:{size:int | size >= 0} -> {r:text | bytes r && text_length r = \
          size}";
       universals = [ "size" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec string_size (size : int) : text =
  if size = 0 then End else Byte (int_range_inc 0 255, string_size (size - 1))

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {r:text | bytes r && 0 <= text_length r && \
          text_length r < 32}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] operation_proto_gen (unit_value : unit) : text =
  let tag = int_range_inc 0 1 in
  let n = if tag = 0 then 0 else int_range_inc 0 31 in
  string_size n

let operation_gen (block_hash_gen : unit -> int) (_u : unit) : operation =
  let branch = block_hash_gen () in
  Operation (branch, operation_proto_gen ())

let[@refined.predicate] valid_rational (v : rational) : bool =
  match v with Rational (p, q) -> 0 < q && q <= 2147483647 && 0 <= p && p <= q

let[@refined.logic] numerator (v : rational) : int =
  match v with Rational (p, _) -> p

let[@refined.logic] denominator (v : rational) : int =
  match v with Rational (_, q) -> q

[@@@refined.axiom
{
  name = "rational_elim";
  quantifiers = [ ("forall", "v", "rational") ];
  body =
    "implies (valid_rational v) (v = Rational (numerator v, denominator v) && \
     0 < denominator v && denominator v <= 2147483647 && 0 <= numerator v && \
     numerator v <= denominator v)";
}]

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:rational | valid_rational r}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] q_in_0_1 (unit_value : unit) : rational =
  let q = int_range_inc 1 2147483647 in
  let p = int_range_inc 0 q in
  Rational (p, q)

let[@refined.predicate] rec sized_rationals (v : rationals) (n : int) : bool =
  match v with
  | No_rationals -> n = 0
  | More_rationals (h, t) ->
      n > 0 && valid_rational h && sized_rationals t (n - 1)

let[@refined.logic] rational_head (v : rationals) : rational =
  match v with No_rationals -> Rational (0, 1) | More_rationals (h, _) -> h

let[@refined.logic] rational_tail (v : rationals) : rationals =
  match v with No_rationals -> No_rationals | More_rationals (_, t) -> t

let[@refined.logic] rec rational_count (v : rationals) : int =
  match v with
  | No_rationals -> 0
  | More_rationals (_, t) -> 1 + rational_count t

[@@@refined.axiom
{
  name = "rationals_elim";
  quantifiers = [ ("forall", "v", "rationals"); ("forall", "n", "int") ];
  body =
    "implies (sized_rationals v n) ((n = 0 && v = No_rationals) || (n > 0 && v \
     = More_rationals (rational_head v, rational_tail v) && valid_rational \
     (rational_head v) && sized_rationals (rational_tail v) (n - 1)))";
}]

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> {r:rationals | sized_rationals r size}";
       universals = [ "size" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec small_list (size : int) : rationals =
  if size = 0 then No_rationals
  else More_rationals (q_in_0_1 (), small_list (size - 1))

let[@refined.predicate] wf_priority (v : priority) : bool =
  match v with
  | High -> true
  | Medium -> true
  | Low l -> rational_count l <= 100 && sized_rationals l (rational_count l)

let[@refined.logic] weights (v : priority) : rationals =
  match v with Low l -> l | _ -> No_rationals

[@@@refined.axiom
{
  name = "priority_elim";
  quantifiers = [ ("forall", "v", "priority") ];
  body =
    "implies (wf_priority v) (v = High || v = Medium || (v = Low (weights v) \
     && 0 <= rational_count (weights v) && rational_count (weights v) <= 100 \
     && sized_rationals (weights v) (rational_count (weights v))))";
}]

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:priority | wf_priority r}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] priority_gen (unit_value : unit) : priority =
  let tag = int_range_inc 0 2 in
  if tag = 0 then High
  else if tag = 1 then Medium
  else Low (small_list (int_range_inc 0 100))

type blocks = Nil | Cons of int * blocks
type tree = Leaf of int | Unary of int * tree | Binary of int * tree * tree
type result_tree = None_tree | Some_tree of tree

let[@refined.logic] rec block_length (b : blocks) : int =
  match b with Nil -> 0 | Cons (_, t) -> 1 + block_length t

let rec append (a : blocks) (b : blocks) : blocks =
  match a with Nil -> b | Cons (h, t) -> Cons (h, append t b)

let rec preorder (t : tree) : blocks =
  match t with
  | Leaf x -> Cons (x, Nil)
  | Unary (x, t) -> Cons (x, preorder t)
  | Binary (x, l, r) -> Cons (x, append (preorder l) (preorder r))

let[@refined.logic] rec prefix (b : blocks) (n : int) : blocks =
  if n = 0 then Nil
  else match b with Nil -> Nil | Cons (h, t) -> Cons (h, prefix t (n - 1))

let[@refined.logic] rec suffix (b : blocks) (n : int) : blocks =
  if n = 0 then b
  else match b with Nil -> Nil | Cons (_, t) -> suffix t (n - 1)

let[@refined.predicate] tree_target (v : result_tree) (b : blocks) : bool =
  match v with None_tree -> b = Nil | Some_tree t -> preorder t = b

let[@refined.logic] tree_value (v : result_tree) : tree =
  match v with None_tree -> Leaf 0 | Some_tree t -> t

let[@refined.logic] left_tree (t : tree) : tree =
  match t with Leaf x -> Leaf x | Unary (_, t) -> t | Binary (_, l, _) -> l

let[@refined.logic] right_tree (t : tree) : tree =
  match t with Leaf x -> Leaf x | Unary (_, t) -> t | Binary (_, _, r) -> r

let[@refined.logic] rec tree_size (t : tree) : int =
  match t with
  | Leaf _ -> 1
  | Unary (_, t) -> 1 + tree_size t
  | Binary (_, l, r) -> 1 + tree_size l + tree_size r

[@@@refined.axiom
{ name = "block_nil"; quantifiers = []; body = "block_length Nil = 0" }]

[@@@refined.axiom
{
  name = "block_cons";
  quantifiers = [ ("forall", "x", "int"); ("forall", "t", "blocks") ];
  body = "block_length (Cons (x,t)) = 1 + block_length t && block_length t >= 0";
}]

[@@@refined.axiom
{
  name = "split_lengths";
  quantifiers = [ ("forall", "b", "blocks"); ("forall", "n", "int") ];
  body =
    "implies (0 <= n && n <= block_length b) (block_length (prefix b n) = n && \
     block_length (suffix b n) = block_length b - n)";
}]

[@@@refined.axiom
{
  name = "tree_nil";
  quantifiers = [ ("forall", "v", "result_tree") ];
  body = "implies (tree_target v Nil) (v = None_tree)";
}]

[@@@refined.axiom
{
  name = "tree_single";
  quantifiers = [ ("forall", "v", "result_tree"); ("forall", "x", "int") ];
  body = "implies (tree_target v (Cons (x,Nil))) (v = Some_tree (Leaf x))";
}]

[@@@refined.axiom
{
  name = "block_empty";
  quantifiers = [ ("forall", "b", "blocks") ];
  body = "implies (block_length b = 0) (b = Nil)";
}]

[@@@refined.axiom
{
  name = "tree_cons";
  quantifiers =
    [
      ("forall", "v", "result_tree");
      ("forall", "x", "int");
      ("forall", "b", "blocks");
    ];
  body =
    "implies (block_length b > 0 && tree_target v (Cons (x,b))) (v = Some_tree \
     (tree_value v) && ((tree_value v = Unary (x,left_tree (tree_value v)) && \
     tree_target (Some_tree (left_tree (tree_value v))) b) || (tree_value v = \
     Binary (x,left_tree (tree_value v),right_tree (tree_value v)) && 0 < \
     tree_size (left_tree (tree_value v)) && tree_size (left_tree (tree_value \
     v)) < block_length b && tree_target (Some_tree (left_tree (tree_value \
     v))) (prefix b (tree_size (left_tree (tree_value v)))) && tree_target \
     (Some_tree (right_tree (tree_value v))) (suffix b (tree_size (left_tree \
     (tree_value v)))))))";
}]

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> blocks:{blocks:blocks | block_length \
          blocks = size} -> {r:result_tree | tree_target r blocks}";
       universals = [ "size"; "blocks" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec tezos_tree_gen (size : int) (blocks : blocks) :
    result_tree =
  match blocks with
  | Nil -> None_tree
  | Cons (x, xs) -> (
      if block_length xs = 0 then Some_tree (Leaf x)
      else if bool_gen () then
        let sub = tezos_tree_gen (size - 1) xs in
        match sub with
        | None_tree -> Some_tree (Leaf x)
        | Some_tree t -> Some_tree (Unary (x, t))
      else
        let n = int_range_inc 0 (size - 1) in
        let left = prefix xs n in
        let right = suffix xs n in
        let lt = tezos_tree_gen n left in
        let rt = tezos_tree_gen (size - 1 - n) right in
        match lt with
        | None_tree -> (
            match rt with
            | None_tree -> Some_tree (Leaf x)
            | Some_tree t -> Some_tree (Unary (x, t)))
        | Some_tree l -> (
            match rt with
            | None_tree -> Some_tree (Unary (x, l))
            | Some_tree r -> Some_tree (Binary (x, l, r))))

let runtime_examples (_u : unit) =
  let input = Cons (1, Cons (2, Cons (3, Nil))) in
  tree_target (tezos_tree_gen 3 input) input
  && tree_target (tezos_tree_gen 0 Nil) Nil
  && text_length (string_size 31) = 31
  && valid_rational (q_in_0_1 ())
  && sized_rationals (small_list 5) 5
