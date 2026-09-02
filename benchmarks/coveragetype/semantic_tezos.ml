(* SPDX-License-Identifier: MIT
   Executable semantic model for data/monad/tezos.ml and tezos_test.ml. *)

type rational = Rational of int * int
type rationals = No_rationals | More_rationals of rational * rationals
type priority = High | Medium | Low of rationals
type blocks = No_blocks | More_blocks of int * blocks
type tezos_tree = Tezos_leaf of int | Tezos_node1 of int * tezos_tree | Tezos_node2 of int * tezos_tree * tezos_tree
type generated_tree = No_tree | Some_tree of tezos_tree

type tezos_report = Tezos_report of bool * bool * bool * bool

let valid_proto_length length = 0 <= length && length < 32

let valid_rational value =
  match value with Rational (numerator, denominator) ->
    0 <= numerator && numerator <= denominator && denominator >= 1

let rec rational_list_length values =
  match values with
  | No_rationals -> 0
  | More_rationals (_, tail) -> 1 + rational_list_length tail

let rec valid_rationals values =
  match values with
  | No_rationals -> true
  | More_rationals (head, tail) -> valid_rational head && valid_rationals tail

let valid_priority value =
  match value with
  | High -> true
  | Medium -> true
  | Low weights -> valid_rationals weights && rational_list_length weights <= 100

let rec equal_blocks left right =
  match left with
  | No_blocks -> ( match right with No_blocks -> true | More_blocks (_, _) -> false )
  | More_blocks (left_head, left_tail) -> (
      match right with
      | No_blocks -> false
      | More_blocks (right_head, right_tail) ->
          left_head = right_head && equal_blocks left_tail right_tail)

let rec append_blocks left right =
  match left with
  | No_blocks -> right
  | More_blocks (head, tail) -> More_blocks (head, append_blocks tail right)

let rec tree_blocks value =
  match value with
  | Tezos_leaf block -> More_blocks (block, No_blocks)
  | Tezos_node1 (block, child) -> More_blocks (block, tree_blocks child)
  | Tezos_node2 (block, left, right) ->
      More_blocks (block, append_blocks (tree_blocks left) (tree_blocks right))

let valid_tree_generation input result =
  match result with
  | No_tree -> input = No_blocks
  | Some_tree tree -> equal_blocks input (tree_blocks tree)

let build_tezos_report (_unit : unit) =
  let weights =
    More_rationals
      (Rational (0, 1), More_rationals (Rational (2, 3), No_rationals))
  in
  let input = More_blocks (1, More_blocks (2, More_blocks (3, No_blocks))) in
  let output =
    Some_tree
      (Tezos_node2 (1, Tezos_leaf 2, Tezos_leaf 3))
  in
  Tezos_report
    ( valid_proto_length 31,
      valid_rational (Rational (2, 3)),
      valid_priority (Low weights),
      valid_tree_generation input output )

let[@refined.predicate] valid_tezos_report (report : tezos_report) : bool =
  match report with
  | Tezos_report (proto_ok, rational_ok, priority_ok, tree_ok) ->
      proto_ok && rational_ok && priority_ok && tree_ok

[@@@refined.axiom
{
  name = "tezos_report_intro";
  quantifiers = [];
  body = "valid_tezos_report (Tezos_report (true, true, true, true))";
}]

[@@@refined.axiom
{
  name = "tezos_report_elim";
  quantifiers = [ ("forall", "report", "tezos_report") ];
  body =
    "implies (valid_tezos_report report) (report = Tezos_report (true, true, \
     true, true))";
}]

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {result:tezos_report | valid_tezos_report result}";
       witness_relation = "result = Tezos_report (true, true, true, true)";
     }] tezos (unit_value : unit) : tezos_report =
  let _unused_unit = unit_value in
  Tezos_report (true, true, true, true)

let runtime_examples (_unit : unit) =
  let Tezos_report (proto_ok, rational_ok, priority_ok, tree_ok) =
    build_tezos_report _unit
  in
  proto_ok && rational_ok && priority_ok && tree_ok
  && not (valid_proto_length 32)
  && not (valid_rational (Rational (4, 3)))
  && not (valid_rational (Rational (0, 0)))
  && not
       (valid_priority
          (Low (More_rationals (Rational (2, 1), No_rationals))))
  && valid_tree_generation No_blocks No_tree
  && not
       (valid_tree_generation (More_blocks (1, No_blocks))
          (Some_tree (Tezos_leaf 2)))
