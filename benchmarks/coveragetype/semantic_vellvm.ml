(* SPDX-License-Identifier: MIT
   Executable semantic model of data/monad/vellvm.ml. *)

type llvm_type =
  | Type_i of int
  | Type_void
  | Type_vector of int * llvm_type
  | Type_array of int * llvm_type
  | Type_others

type dvalue =
  | D_int of int * int
  | D_none
  | D_vector of llvm_type * dvalues
  | D_array of llvm_type * dvalues
  | D_error

and dvalues = No_values | More_values of dvalue * dvalues

let rec value_count values =
  match values with
  | No_values -> 0
  | More_values (_, tail) -> 1 + value_count tail

let valid_integer width number =
  if width = 1 then 0 <= number && number <= 1
  else if width = 8 then 0 <= number && number <= 255
  else if width = 32 || width = 64 then 0 <= number && number <= 10000
  else false

let rec all_typed values expected =
  match values with
  | No_values -> true
  | More_values (head, tail) ->
      llvm_typing head expected && all_typed tail expected

and llvm_typing value expected =
  match expected with
  | Type_i width -> (
      match value with
      | D_int (actual_width, number) ->
          actual_width = width && valid_integer width number
      | _ -> false)
  | Type_void -> value = D_none
  | Type_vector (size, element_type) -> (
      match value with
      | D_vector (actual_type, values) ->
          actual_type = expected && size >= 0
          && value_count values = size
          && all_typed values element_type
      | _ -> false)
  | Type_array (size, element_type) -> (
      match value with
      | D_array (actual_type, values) ->
          actual_type = expected && size >= 0
          && value_count values = size
          && all_typed values element_type
      | _ -> false)
  | Type_others -> false

let[@refined.predicate] typed (v : dvalue) (t : llvm_type) : bool =
  llvm_typing v t

let[@refined.predicate] typed_list (v : dvalues) (n : int) (t : llvm_type) :
    bool =
  value_count v = n && all_typed v t

let[@refined.logic] rec type_depth (t : llvm_type) : int =
  match t with
  | Type_vector (_, t) -> 1 + type_depth t
  | Type_array (_, t) -> 1 + type_depth t
  | _ -> 0

let[@refined.logic] integer (v : dvalue) : int =
  match v with D_int (_, n) -> n | _ -> 0

let[@refined.logic] contents (v : dvalue) : dvalues =
  match v with D_vector (_, l) -> l | D_array (_, l) -> l | _ -> No_values

let[@refined.logic] value_head (v : dvalues) : dvalue =
  match v with No_values -> D_none | More_values (h, _) -> h

let[@refined.logic] value_tail (v : dvalues) : dvalues =
  match v with No_values -> No_values | More_values (_, t) -> t

[@@@refined.axiom
{
  name = "type_nonnegative";
  quantifiers = [ ("forall", "t", "llvm_type") ];
  body = "type_depth t >= 0";
}]

[@@@refined.axiom
{
  name = "Type_vector_depth";
  quantifiers = [ ("forall", "n", "int"); ("forall", "t", "llvm_type") ];
  body = "type_depth (Type_vector (n,t)) = 1 + type_depth t";
}]

[@@@refined.axiom
{
  name = "Type_array_depth";
  quantifiers = [ ("forall", "n", "int"); ("forall", "t", "llvm_type") ];
  body = "type_depth (Type_array (n,t)) = 1 + type_depth t";
}]

[@@@refined.axiom
{
  name = "typed_integer";
  quantifiers = [ ("forall", "v", "dvalue"); ("forall", "w", "int") ];
  body =
    "implies (typed v (Type_i w)) (v = D_int (w,integer v) && ((w = 1 && 0 <= \
     integer v && integer v <= 1) || (w = 8 && 0 <= integer v && integer v <= \
     255) || ((w = 32 || w = 64) && 0 <= integer v && integer v <= 10000)))";
}]

[@@@refined.axiom
{
  name = "typed_void";
  quantifiers = [ ("forall", "v", "dvalue") ];
  body = "implies (typed v Type_void) (v = D_none)";
}]

[@@@refined.axiom
{
  name = "typed_other";
  quantifiers = [ ("forall", "v", "dvalue") ];
  body = "not (typed v Type_others)";
}]

[@@@refined.axiom
{
  name = "Type_vector_elim";
  quantifiers =
    [
      ("forall", "v", "dvalue");
      ("forall", "n", "int");
      ("forall", "t", "llvm_type");
    ];
  body =
    "implies (typed v (Type_vector (n,t))) (n >= 0 && v = D_vector \
     (Type_vector (n,t),contents v) && typed_list (contents v) n t)";
}]

[@@@refined.axiom
{
  name = "Type_array_elim";
  quantifiers =
    [
      ("forall", "v", "dvalue");
      ("forall", "n", "int");
      ("forall", "t", "llvm_type");
    ];
  body =
    "implies (typed v (Type_array (n,t))) (n >= 0 && v = D_array (Type_array \
     (n,t),contents v) && typed_list (contents v) n t)";
}]

[@@@refined.axiom
{
  name = "typed_list_elim";
  quantifiers =
    [
      ("forall", "v", "dvalues");
      ("forall", "n", "int");
      ("forall", "t", "llvm_type");
    ];
  body =
    "implies (typed_list v n t) ((n = 0 && v = No_values) || (n > 0 && v = \
     More_values (value_head v,value_tail v) && typed (value_head v) t && \
     typed_list (value_tail v) (n - 1) t))";
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
         "depth:{depth:int | depth >= 0} -> count:{count:int | count >= 0} -> \
          expected:{expected:llvm_type | type_depth expected = depth} -> \
          {r:dvalue | typed r expected}";
       universals = [ "depth"; "count"; "expected" ];
       witness_relation = "true";
     }]
   [@refined.measure "depth, count"] rec gen_uvalue (depth : int) (count : int)
    (expected : llvm_type) : dvalue =
  match expected with
  | Type_i width ->
      if width = 1 then D_int (1, if bool_gen () then 1 else 0)
      else if width = 8 then D_int (8, int_range_inc 0 255)
      else if width = 32 then D_int (32, int_range_inc 0 10000)
      else if width = 64 then D_int (64, int_range_inc 0 10000)
      else raise Reject
  | Type_void -> D_none
  | Type_vector (n, t) ->
      if n < 0 then raise Reject
      else D_vector (expected, gen_values (depth - 1) n t)
  | Type_array (n, t) ->
      if n < 0 then raise Reject
      else D_array (expected, gen_values (depth - 1) n t)
  | Type_others -> raise Reject

and[@refined.coverage
     {
       type_ =
         "depth:{depth:int | depth >= 0} -> count:{count:int | count >= 0} -> \
          expected:{expected:llvm_type | type_depth expected = depth} -> \
          {r:dvalues | typed_list r count expected}";
       universals = [ "depth"; "count"; "expected" ];
       witness_relation = "true";
     }]
   [@refined.measure "depth, count"] gen_values (depth : int) (count : int)
    (expected : llvm_type) : dvalues =
  if count = 0 then No_values
  else
    let h = gen_uvalue depth 0 expected in
    More_values (h, gen_values depth (count - 1) expected)

let runtime_examples (_u : unit) =
  let t = Type_vector (2, Type_array (3, Type_i 8)) in
  typed (gen_uvalue 2 0 t) t
  && typed (gen_uvalue 0 0 Type_void) Type_void
  && (try
        ignore (gen_uvalue 0 0 (Type_i 16));
        false
      with Reject -> true)
  && not (typed (D_int (8, 256)) (Type_i 8))
