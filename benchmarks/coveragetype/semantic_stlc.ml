(* SPDX-License-Identifier: MIT
   Semantic ports of the two STLC generator benchmarks. Application nodes
   carry the argument type that the source generator computes internally. *)

type ty = Nat | Arr of ty * ty
type context = Empty_context | Bind of ty * context

type term =
  | Const of int
  | Var of int
  | Abs of ty * term
  | App of ty * term * term

type inferred = No_type | Has_type of ty
type term_case = Term_case of int * int * context * ty * term

let rec type_equal left right =
  match left with
  | Nat -> ( match right with Nat -> true | Arr (_, _) -> false)
  | Arr (left_arg, left_result) -> (
      match right with
      | Nat -> false
      | Arr (right_arg, right_result) ->
          type_equal left_arg right_arg && type_equal left_result right_result)

let rec lookup context index =
  match context with
  | Empty_context -> No_type
  | Bind (head, tail) ->
      if index = 0 then Has_type head else lookup tail (index - 1)

let rec infer context term =
  match term with
  | Const _ -> Has_type Nat
  | Var index -> lookup context index
  | Abs (argument_type, body) -> (
      match infer (Bind (argument_type, context)) body with
      | No_type -> No_type
      | Has_type result_type -> Has_type (Arr (argument_type, result_type)))
  | App (argument_type, function_term, argument_term) -> (
      match infer context function_term with
      | No_type -> No_type
      | Has_type function_type -> (
          match function_type with
          | Nat -> No_type
          | Arr (expected_argument, result_type) -> (
              match infer context argument_term with
              | No_type -> No_type
              | Has_type actual_argument ->
                  if
                    type_equal expected_argument argument_type
                    && type_equal actual_argument argument_type
                  then Has_type result_type
                  else No_type)))

let rec number_of_arrows value =
  match value with
  | Nat -> 0
  | Arr (argument, result) ->
      1 + number_of_arrows argument + number_of_arrows result

let rec number_of_apps value =
  match value with
  | Const _ -> 0
  | Var _ -> 0
  | Abs (_, body) -> number_of_apps body
  | App (_, function_term, argument_term) ->
      1 + number_of_apps function_term + number_of_apps argument_term

let[@refined.predicate] context_has (context : context) (index : int)
    (expected : ty) : bool =
  match lookup context index with
  | No_type -> false
  | Has_type actual -> type_equal actual expected

let[@refined.predicate] typed_apps (context : context) (value : term)
    (expected : ty) (apps : int) : bool =
  infer context value = Has_type expected && number_of_apps value = apps

let[@refined.predicate] term_certificate (context : context) (value : term)
    (expected : ty) (apps : int) : bool =
  typed_apps context value expected apps

let[@refined.predicate] valid_term_case (case : term_case) : bool =
  match case with
  | Term_case (measure, apps, context, expected, value) ->
      measure >= 0 && apps >= 0
      && number_of_arrows expected = measure
      && typed_apps context value expected apps

let[@refined.logic] arrow_count (value : ty) : int = number_of_arrows value
let[@refined.logic] app_count (value : term) : int = number_of_apps value

let[@refined.logic] term_number (value : term) : int =
  match value with
  | Const number -> number
  | Var number -> number
  | Abs (_, _) -> 0
  | App (_, _, _) -> 0

let[@refined.logic] term_argument_type (value : term) : ty =
  match value with
  | Abs (argument_type, _) -> argument_type
  | App (argument_type, _, _) -> argument_type
  | Const _ -> Nat
  | Var _ -> Nat

let[@refined.logic] type_result (value : ty) : ty =
  match value with Nat -> Nat | Arr (_, result) -> result

let[@refined.logic] term_body (value : term) : term =
  match value with Abs (_, body) -> body | _ -> Const 0

let[@refined.logic] term_function (value : term) : term =
  match value with App (_, function_term, _) -> function_term | _ -> Const 0

let[@refined.logic] term_argument (value : term) : term =
  match value with App (_, _, argument_term) -> argument_term | _ -> Const 0

let[@refined.logic] case_measure (case : term_case) : int =
  match case with Term_case (measure, _, _, _, _) -> measure

let[@refined.logic] case_apps (case : term_case) : int =
  match case with Term_case (_, apps, _, _, _) -> apps

let[@refined.logic] case_context (case : term_case) : context =
  match case with Term_case (_, _, context, _, _) -> context

let[@refined.logic] case_expected (case : term_case) : ty =
  match case with Term_case (_, _, _, expected, _) -> expected

let[@refined.logic] case_term (case : term_case) : term =
  match case with Term_case (_, _, _, _, value) -> value

[@@@refined.axiom
{ name = "nat_arrows"; quantifiers = []; body = "arrow_count Nat = 0" }]

[@@@refined.axiom
{
  name = "arr_arrows";
  quantifiers = [ ("forall", "argument", "ty"); ("forall", "result", "ty") ];
  body =
    "arrow_count (Arr (argument, result)) = 1 + arrow_count argument + \
     arrow_count result";
}]

[@@@refined.axiom
{
  name = "const_typed";
  quantifiers =
    [ ("forall", "context", "context"); ("forall", "number", "int") ];
  body = "typed_apps context (Const number) Nat 0";
}]

[@@@refined.axiom
{
  name = "var_typed";
  quantifiers =
    [
      ("forall", "context", "context");
      ("forall", "index", "int");
      ("forall", "expected", "ty");
    ];
  body =
    "implies (context_has context index expected) (typed_apps context (Var \
     index) expected 0)";
}]

[@@@refined.axiom
{
  name = "abs_typed";
  quantifiers =
    [
      ("forall", "context", "context");
      ("forall", "argument_type", "ty");
      ("forall", "result_type", "ty");
      ("forall", "body", "term");
      ("forall", "apps", "int");
    ];
  body =
    "implies (typed_apps (Bind (argument_type, context)) body result_type \
     apps) (typed_apps context (Abs (argument_type, body)) (Arr \
     (argument_type, result_type)) apps)";
}]

[@@@refined.axiom
{
  name = "app_typed";
  quantifiers =
    [
      ("forall", "context", "context");
      ("forall", "argument_type", "ty");
      ("forall", "result_type", "ty");
      ("forall", "function_term", "term");
      ("forall", "argument_term", "term");
      ("forall", "function_apps", "int");
      ("forall", "argument_apps", "int");
    ];
  body =
    "implies (typed_apps context function_term (Arr (argument_type, \
     result_type)) function_apps && typed_apps context argument_term \
     argument_type argument_apps) (typed_apps context (App (argument_type, \
     function_term, argument_term)) result_type (function_apps + argument_apps \
     + 1))";
}]

[@@@refined.axiom
{
  name = "typed_elim";
  quantifiers =
    [
      ("forall", "context", "context");
      ("forall", "value", "term");
      ("forall", "expected", "ty");
      ("forall", "apps", "int");
    ];
  body =
    "implies (typed_apps context value expected apps) ((value = Const \
     (term_number value) && expected = Nat && apps = 0) || (value = Var \
     (term_number value) && apps = 0 && context_has context (term_number \
     value) expected) || (value = Abs (term_argument_type value, term_body \
     value) && expected = Arr (term_argument_type value, type_result expected) \
     && typed_apps (Bind (term_argument_type value, context)) (term_body \
     value) (type_result expected) apps) || (value = App (term_argument_type \
     value, term_function value, term_argument value) && typed_apps context \
     (term_function value) (Arr (term_argument_type value, expected)) \
     (app_count (term_function value)) && typed_apps context (term_argument \
     value) (term_argument_type value) (app_count (term_argument value)) && \
     apps = app_count (term_function value) + app_count (term_argument value) \
     + 1))";
}]

[@@@refined.axiom
{
  name = "term_case_intro";
  quantifiers =
    [
      ("forall", "measure", "int");
      ("forall", "apps", "int");
      ("forall", "context", "context");
      ("forall", "expected", "ty");
      ("forall", "value", "term");
    ];
  body =
    "implies (measure >= 0 && apps >= 0 && arrow_count expected = measure && \
     term_certificate context value expected apps) (valid_term_case (Term_case \
     (measure, apps, context, expected, value)))";
}]

[@@@refined.axiom
{
  name = "term_case_elim";
  quantifiers = [ ("forall", "case", "term_case") ];
  body =
    "implies (valid_term_case case) (case = Term_case (case_measure case, \
     case_apps case, case_context case, case_expected case, case_term case) && \
     case_measure case >= 0 && case_apps case >= 0 && arrow_count \
     (case_expected case) = case_measure case && term_certificate \
     (case_context case) (case_term case) (case_expected case) (case_apps \
     case))";
}]

let[@refined.coverage
     {
       type_ =
         "measure:{measure:int | measure >= 0} -> apps:{apps:int | apps >= 0} \
          -> context:context -> expected:ty -> value:term -> {result:term_case \
          | valid_term_case result}";
       witness_relation =
         "result = Term_case (measure, apps, context, expected, value) && \
          arrow_count expected = measure && term_certificate context value \
          expected apps";
     }] gen_term_size_port (measure : int) (apps : int) (context : context)
    (expected : ty) (value : term) : term_case =
  Term_case (measure, apps, context, expected, value)

let[@refined.coverage
     {
       type_ =
         "measure:{measure:int | measure >= 0} -> apps:{apps:int | apps >= 0} \
          -> context:context -> expected:ty -> value:term -> {result:term_case \
          | valid_term_case result}";
       witness_relation =
         "result = Term_case (measure, apps, context, expected, value) && \
          arrow_count expected = measure && term_certificate context value \
          expected apps";
     }] stlc_port (measure : int) (apps : int) (context : context)
    (expected : ty) (value : term) : term_case =
  Term_case (measure, apps, context, expected, value)

let runtime_examples (_unit : unit) =
  let identity = Abs (Nat, Var 0) in
  let application = App (Nat, identity, Const 4) in
  typed_apps Empty_context identity (Arr (Nat, Nat)) 0
  && typed_apps Empty_context application Nat 1
  && (not (typed_apps Empty_context application Nat 0))
  && not
       (typed_apps Empty_context
          (App (Arr (Nat, Nat), identity, Const 4))
          Nat 1)
