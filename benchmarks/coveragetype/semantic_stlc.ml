(* SPDX-License-Identifier: MIT
   Recursive ports of the two STLC generator benchmarks at the pinned revision.
   Application nodes carry the argument type computed by the source generator.
   Coverage needs decomposition, not recursive constructor introduction axioms;
   the latter unnecessarily saturate the solver with new typed terms. *)

type ty = Nat | Arr of ty * ty
type context = Empty_context | Bind of ty * context

type term =
  | Const of int
  | Var of int
  | Abs of ty * term
  | App of ty * term * term

type inferred = No_type | Has_type of ty

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
     + 1 && app_count (term_function value) >= 0 && app_count (term_function \
     value) < apps && app_count (term_argument value) >= 0 && app_count \
     (term_argument value) < apps - app_count (term_function value)))";
}]

[@@@refined.axiom
{
  name = "arrows_nonnegative";
  quantifiers = [ ("forall", "value", "ty") ];
  body = "arrow_count value >= 0";
}]

[@@@refined.axiom
{
  name = "apps_nonnegative";
  quantifiers = [ ("forall", "value", "term") ];
  body = "app_count value >= 0";
}]

[@@@refined.axiom
{
  name = "typed_app_count";
  quantifiers =
    [
      ("forall", "context", "context");
      ("forall", "value", "term");
      ("forall", "expected", "ty");
      ("forall", "apps", "int");
    ];
  body =
    "implies (typed_apps context value expected apps) (app_count value = apps \
     && apps >= 0)";
}]

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = true

(* gen_type is an explicit library primitive in upstream gen_term_size.ml.
   The choice marker models its complete type image, as it models int_gen. *)
let[@refined.choose] gen_type (_unit : unit) : ty = Nat

let[@refined.coverage
     {
       type_ =
         "lower:int -> upper:{upper:int | lower < upper} -> {r:int | lower <= \
          r && r < upper}";
       witness_relation = "true";
       universals = [ "lower"; "upper" ];
     }] int_range_inex (lower : int) (upper : int) : int =
  let candidate = int_gen () in
  if candidate < lower then lower
  else if candidate >= upper then upper - 1
  else candidate

(* A nondeterministic index plus the same lookup filter has the successful
   image of upstream vars_with_type's nondeterministic context traversal. *)
let[@refined.coverage
     {
       type_ =
         "context:context -> expected:ty -> {r:term | typed_apps context r \
          expected 0 && r = Var (term_number r)}";
       witness_relation = "true";
       universals = [ "context"; "expected" ];
     }] vars_with_type (context : context) (expected : ty) : term =
  let index = int_gen () in
  if context_has context index expected then Var index else raise Reject

let[@refined.coverage
     {
       type_ =
         "measure:{measure:int | measure >= 0} -> context:context -> \
          expected:{t:ty | arrow_count t = measure} -> {r:term | typed_apps \
          context r expected 0}";
       witness_relation = "true";
       universals = [ "measure"; "context"; "expected" ];
     }]
   [@refined.measure "measure"] rec gen_term_no_app (measure : int)
    (context : context) (expected : ty) : term =
  if bool_gen () then
    match expected with
    | Nat -> Const (int_gen ())
    | Arr (argument_type, result_type) ->
        Abs
          ( argument_type,
            gen_term_no_app (arrow_count result_type)
              (Bind (argument_type, context))
              result_type )
  else vars_with_type context expected

let[@refined.coverage
     {
       type_ =
         "measure:{measure:int | measure >= 0} -> apps:{apps:int | apps >= 0} \
          -> context:context -> expected:{t:ty | arrow_count t = measure} -> \
          {r:term | typed_apps context r expected apps}";
       witness_relation = "true";
       universals = [ "measure"; "apps"; "context"; "expected" ];
     }]
   [@refined.measure "apps, measure"] rec gen_term_size_port (measure : int)
    (apps : int) (context : context) (expected : ty) : term =
  if apps = 0 then gen_term_no_app measure context expected
  else if bool_gen () then
    let argument_type = gen_type () in
    let function_apps = int_range_inex 0 apps in
    let argument_apps = int_range_inex 0 (apps - function_apps) in
    let function_type = Arr (argument_type, expected) in
    let function_term =
      gen_term_size_port
        (arrow_count function_type)
        function_apps context function_type
    in
    let argument_term =
      gen_term_size_port
        (arrow_count argument_type)
        argument_apps context argument_type
    in
    App (argument_type, function_term, argument_term)
  else
    match expected with
    | Nat -> raise Reject
    | Arr (argument_type, result_type) ->
        Abs
          ( argument_type,
            gen_term_size_port (arrow_count result_type) apps
              (Bind (argument_type, context))
              result_type )

(* The monadic artifact uses the same algorithm with a supplied measure.
   A lexicographic (application count, arrow count) measure makes the descent
   explicit without an additional trusted calculate_measure library. *)
let[@refined.coverage
     {
       type_ =
         "measure:{measure:int | measure >= 0} -> apps:{apps:int | apps >= 0} \
          -> context:context -> expected:{t:ty | arrow_count t = measure} -> \
          {r:term | typed_apps context r expected apps}";
       witness_relation = "true";
       universals = [ "measure"; "apps"; "context"; "expected" ];
     }] stlc_port (measure : int) (apps : int) (context : context)
    (expected : ty) : term =
  gen_term_size_port measure apps context expected

let runtime_examples (_unit : unit) : bool =
  let natural = gen_term_size_port 0 0 Empty_context Nat in
  let identity_type = Arr (Nat, Nat) in
  let abstraction = gen_term_no_app 1 Empty_context identity_type in
  let application = gen_term_size_port 0 1 Empty_context Nat in
  let deeper = stlc_port 1 2 Empty_context identity_type in
  typed_apps Empty_context natural Nat 0
  && typed_apps Empty_context abstraction identity_type 0
  && typed_apps Empty_context application Nat 1
  && infer Empty_context deeper = Has_type identity_type
  && number_of_apps deeper <= 2
  && not (typed_apps Empty_context (App (Nat, Const 0, Const 1)) Nat 1)
