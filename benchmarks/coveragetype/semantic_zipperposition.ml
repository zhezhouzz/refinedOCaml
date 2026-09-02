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

let[@refined.predicate] valid_term_case (case : term_case) : bool =
  match case with
  | Term_case (expected, value) -> expected >= 1 && sized_term value expected

let[@refined.logic] case_size (case : term_case) : int =
  match case with Term_case (expected, _) -> expected

let[@refined.logic] case_term (case : term_case) : term =
  match case with Term_case (_, value) -> value

[@@@refined.axiom
{
  name = "zipper_case_intro";
  quantifiers = [ ("forall", "expected", "int"); ("forall", "value", "term") ];
  body =
    "implies (expected >= 1 && sized_term value expected) (valid_term_case \
     (Term_case (expected, value)))";
}]

[@@@refined.axiom
{
  name = "zipper_case_elim";
  quantifiers = [ ("forall", "case", "term_case") ];
  body =
    "implies (valid_term_case case) (case = Term_case (case_size case, \
     case_term case) && case_size case >= 1 && sized_term (case_term case) \
     (case_size case))";
}]

let[@refined.coverage
     {
       type_ =
         "expected:{expected:int | expected >= 1} -> value:{value:term | \
          sized_term value expected} -> {result:term_case | valid_term_case \
          result}";
       witness_relation = "result = Term_case (expected, value)";
     }] zipperposition (expected : int) (value : term) : term_case =
  Term_case (expected, value)

let runtime_examples (_unit : unit) =
  let left = App_one (2, Var 0) in
  let valid = Ite (Var 1, left, App_two (0, Var 2, Var 3)) in
  let invalid_name = App_one (2, Var 8) in
  let invalid_symbol = App_two (4, Var 0, Var 1) in
  sized_term valid 7
  && (not (sized_term valid 6))
  && (not (wellformed invalid_name))
  && not (wellformed invalid_symbol)
