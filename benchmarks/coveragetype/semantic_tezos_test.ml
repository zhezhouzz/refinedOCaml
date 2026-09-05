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

let runtime_examples (_u : unit) =
  bytes (operation_proto_gen ())
  && text_length (string_size 31) = 31
  && valid_rational (q_in_0_1 ())
  && wf_priority (priority_gen ())
  && sized_rationals (small_list 5) 5
  && not (valid_rational (Rational (4, 3)))
