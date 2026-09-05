(* SPDX-License-Identifier: MIT
   Semantic port of data/monad/zipperposition.ml. Function symbols and variable
   names are represented by their finite generator indices. *)

type term =
  | Var of int
  | App_two of int * term * term
  | App_one of int * term
  | Ite of term * term * term

type term_case = Term_case of int * term

let rec term_size value =
  match value with
  | Var _ -> 1
  | App_two (_, left, right) -> 1 + term_size left + term_size right
  | App_one (_, argument) -> 1 + term_size argument
  | Ite (condition, when_true, when_false) ->
      1 + term_size condition + term_size when_true + term_size when_false

let rec wellformed value =
  match value with
  | Var name -> 0 <= name && name <= 7
  | App_two (symbol, left, right) ->
      (symbol = 0 || symbol = 1) && wellformed left && wellformed right
  | App_one (symbol, argument) ->
      (symbol = 2 || symbol = 3) && wellformed argument
  | Ite (condition, when_true, when_false) ->
      wellformed condition && wellformed when_true && wellformed when_false

let[@refined.predicate] sized_term (value : term) (expected : int) : bool =
  wellformed value && term_size value = expected

let rec height (v : term) : int =
  match v with
  | Var _ -> 1
  | App_one (_, x) -> 1 + height x
  | App_two (_, x, y) -> 1 + max (height x) (height y)
  | Ite (x, y, z) -> 1 + max (height x) (max (height y) (height z))

let[@refined.predicate] fuel_target (v : term) (n : int) : bool =
  wellformed v && height v <= n + 1

let[@refined.logic] name (v : term) : int =
  match v with
  | Var n -> n
  | App_one (n, _) -> n
  | App_two (n, _, _) -> n
  | Ite _ -> 0

let[@refined.logic] first (v : term) : term =
  match v with
  | Var n -> Var n
  | App_one (_, x) -> x
  | App_two (_, x, _) -> x
  | Ite (x, _, _) -> x

let[@refined.logic] second (v : term) : term =
  match v with App_two (_, _, y) -> y | Ite (_, y, _) -> y | _ -> Var 0

let[@refined.logic] third (v : term) : term =
  match v with Ite (_, _, z) -> z | _ -> Var 0

[@@@refined.axiom
{
  name = "fuel_zero";
  quantifiers = [ ("forall", "v", "term"); ("forall", "n", "int") ];
  body =
    "implies (fuel_target v n && n = 0) (v = Var (name v) && 0 <= name v && \
     name v <= 7)";
}]

[@@@refined.axiom
{
  name = "fuel_positive";
  quantifiers = [ ("forall", "v", "term"); ("forall", "n", "int") ];
  body =
    "implies (fuel_target v n && n > 0) ((v = Var (name v) && 0 <= name v && \
     name v <= 7) || (v = App_one (name v,first v) && (name v = 2 || name v = \
     3) && fuel_target (first v) (n - 1)) || (v = App_two (name v,first \
     v,second v) && (name v = 0 || name v = 1) && fuel_target (first v) (n - \
     1) && fuel_target (second v) (n - 1)) || (v = Ite (first v,second v,third \
     v) && fuel_target (first v) (n - 1) && fuel_target (second v) (n - 1) && \
     fuel_target (third v) (n - 1)))";
}]

[@@@refined.axiom
{
  name = "size_implies_fuel";
  quantifiers = [ ("forall", "v", "term"); ("forall", "n", "int") ];
  body = "implies (sized_term v n && n >= 1) (fuel_target v n)";
}]

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let runtime_choices = ref []

let[@refined.choose] bool_gen (_unit : unit) : bool =
  match !runtime_choices with
  | [] -> false
  | h :: t ->
      runtime_choices := t;
      h

let[@refined.coverage
     {
       type_ =
         "lower:int -> upper:{upper:int | lower <= upper} -> {r:int | lower <= \
          r && r <= upper}";
       universals = [ "lower"; "upper" ];
     }] int_range_inc (lower : int) (upper : int) : int =
  let x = int_gen () in
  if x < lower then lower else if x > upper then upper else x

let[@refined.coverage
     {
       type_ = "fuel:{fuel:int | fuel >= 0} -> {r:term | fuel_target r fuel}";
       universals = [ "fuel" ];
       witness_relation = "true";
     }]
   [@refined.measure "fuel"] rec default_fuel (fuel : int) : term =
  if fuel = 0 then Var (int_range_inc 0 7)
  else if bool_gen () then Var (int_range_inc 0 7)
  else if bool_gen () then
    App_two
      ( (if bool_gen () then 0 else 1),
        default_fuel (fuel - 1),
        default_fuel (fuel - 1) )
  else if bool_gen () then
    App_one ((if bool_gen () then 2 else 3), default_fuel (fuel - 1))
  else
    Ite
      (default_fuel (fuel - 1), default_fuel (fuel - 1), default_fuel (fuel - 1))

let[@refined.coverage
     {
       type_ =
         "expected:{expected:int | expected >= 1} -> {r:term | sized_term r \
          expected}";
       universals = [ "expected" ];
     }] zipperposition (expected : int) : term =
  default_fuel expected

let default_examples (_u : unit) =
  fuel_target (default_fuel 0) 0
  && fuel_target (default_fuel 4) 4
  && wellformed (zipperposition 8)
  && not (wellformed (App_one (4, Var 0)))

let runtime_examples (_u : unit) =
  runtime_choices := [];
  let defaults = default_examples () in
  runtime_choices := [ true ];
  let variable = default_fuel 1 = Var 0 in
  runtime_choices := [ false; true; true ];
  let binary = default_fuel 1 = App_two (0, Var 0, Var 0) in
  runtime_choices := [ false; true; false ];
  let binary_other = default_fuel 1 = App_two (1, Var 0, Var 0) in
  runtime_choices := [ false; false; true; true ];
  let unary = default_fuel 1 = App_one (2, Var 0) in
  runtime_choices := [ false; false; true; false ];
  let unary_other = default_fuel 1 = App_one (3, Var 0) in
  runtime_choices := [];
  defaults && variable && binary && binary_other && unary && unary_other
