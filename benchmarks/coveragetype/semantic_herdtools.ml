(* SPDX-License-Identifier: MIT
   Algorithm port at the revision in ../manifest.tsv. *)
type bits = BNil | BCons of bool * bits
type text = Text of int
type real = Real_bits of int

type literal =
  | L_int of int
  | L_bool of bool
  | L_real of real
  | L_bits of bits
  | L_string of text

let[@refined.logic] rec bit_length (v : bits) : int =
  match v with BNil -> 0 | BCons (_, t) -> 1 + bit_length t

let[@refined.logic] bit_head (v : bits) : bool =
  match v with BNil -> false | BCons (h, _) -> h

let[@refined.logic] bit_tail (v : bits) : bits =
  match v with BNil -> BNil | BCons (_, t) -> t

[@@@refined.axiom
{
  name = "bits_elim";
  quantifiers = [ ("forall", "v", "bits") ];
  body =
    "(v = BNil && bit_length v = 0) || (bit_length v > 0 && v = BCons \
     (bit_head v, bit_tail v) && bit_length (bit_tail v) = bit_length v - 1)";
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

let[@refined.choose] text_gen (_u : unit) : text = Text 0
let[@refined.choose] real_gen (_u : unit) : real = Real_bits 0

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {r:bits | bit_length r = size}";
       universals = [ "size" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec bits_gen (size : int) : bits =
  if size = 0 then BNil else BCons (bool_gen (), bits_gen (size - 1))

let[@refined.predicate] wf_literal (v : literal) : bool =
  match v with
  | L_int n -> 0 <= n && n <= 1000
  | L_bool _ -> true
  | L_real _ -> true
  | L_bits b -> bit_length b <= 1000
  | L_string _ -> true

let[@refined.logic] lit_int (v : literal) : int =
  match v with L_int x -> x | _ -> 0

let[@refined.logic] lit_bool (v : literal) : bool =
  match v with L_bool x -> x | _ -> false

let[@refined.logic] lit_real (v : literal) : real =
  match v with L_real x -> x | _ -> Real_bits 0

let[@refined.logic] lit_bits (v : literal) : bits =
  match v with L_bits x -> x | _ -> BNil

let[@refined.logic] lit_string (v : literal) : text =
  match v with L_string x -> x | _ -> Text 0

[@@@refined.axiom
{
  name = "literal_elim";
  quantifiers = [ ("forall", "v", "literal") ];
  body =
    "implies (wf_literal v) ((v = L_int (lit_int v) && 0 <= lit_int v && \
     lit_int v <= 1000) || v = L_bool (lit_bool v) || v = L_real (lit_real v) \
     || (v = L_bits (lit_bits v) && 0 <= bit_length (lit_bits v) && bit_length \
     (lit_bits v) <= 1000) || v = L_string (lit_string v))";
}]

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:literal | wf_literal r}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] herdtools7 (unit_value : unit) : literal =
  let tag = int_range_inc 0 4 in
  if tag = 0 then L_int (int_range_inc 0 1000)
  else if tag = 1 then L_bool (bool_gen ())
  else if tag = 2 then L_real (real_gen ())
  else if tag = 3 then L_bits (bits_gen (int_range_inc 0 1000))
  else L_string (text_gen ())

let runtime_examples (_u : unit) =
  wf_literal (herdtools7 ())
  && bit_length (bits_gen 4) = 4
  && not (wf_literal (L_int 1001))
