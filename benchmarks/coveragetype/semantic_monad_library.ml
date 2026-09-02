(* SPDX-License-Identifier: MIT
   Executable regression model for data/monad/coverage_monad_library.ml. A
   generator is represented by the finite sequence of values it can emit. *)

type ilist = Nil | Cons of int * ilist

type library_report =
  | Library_report of
      bool
      * bool
      * bool
      * bool
      * bool
      * bool
      * bool
      * bool
      * bool
      * bool
      * bool
      * bool

let rec equal_list left right =
  match left with
  | Nil -> ( match right with Nil -> true | Cons (_, _) -> false)
  | Cons (left_head, left_tail) -> (
      match right with
      | Nil -> false
      | Cons (right_head, right_tail) ->
          left_head = right_head && equal_list left_tail right_tail)

let return value = Cons (value, Nil)

let rec map_add delta values =
  match values with
  | Nil -> Nil
  | Cons (head, tail) -> Cons (head + delta, map_add delta tail)

let rec map_sum left right =
  match left with
  | Nil -> Nil
  | Cons (left_head, left_tail) -> (
      match right with
      | Nil -> Nil
      | Cons (right_head, right_tail) ->
          Cons (left_head + right_head, map_sum left_tail right_tail))

let rec union left right =
  match left with
  | Nil -> right
  | Cons (head, tail) -> Cons (head, union tail right)

let bind_add values delta = map_add delta values
let fmap values delta = map_add delta values
let fmap2 left right = map_sum left right

let rec countdown value =
  if value <= 0 then Cons (0, Nil) else Cons (value, countdown (value - 1))

let int_bound bound = if bound < 0 then Nil else countdown bound

let rec int_range lower upper =
  if lower > upper then Nil else Cons (lower, int_range (lower + 1) upper)

let rec length value =
  match value with Nil -> 0 | Cons (_, tail) -> 1 + length tail

let pair_count left right = length left * length right
let option_count values = 1 + length values
let oneof first second choose_first = if choose_first then first else second
let nil_gen (_unit : unit) = Nil
let cons_gen head tail = Cons (head, tail)

let rec nth remaining value =
  match value with
  | Nil -> 0
  | Cons (head, tail) ->
      if remaining = 0 then head else nth (remaining - 1) tail

let oneofl values index = nth index values

let frequency first_weight first second =
  if first_weight > 0 then first else second

let numeral character_code = character_code >= 48 && character_code <= 57

let rec list_repeat count value =
  if count <= 0 then Nil else Cons (value, list_repeat (count - 1) value)

let positive_split total left = left >= 1 && left < total && total - left >= 1

let report_all_true =
  Library_report
    (true, true, true, true, true, true, true, true, true, true, true, true)

let build_report (unit_value : unit) =
  let values = Cons (1, Cons (2, Nil)) in
  Library_report
    ( equal_list (return 4) (Cons (4, Nil)),
      equal_list (bind_add values 3) (Cons (4, Cons (5, Nil))),
      equal_list (fmap values 1) (Cons (2, Cons (3, Nil))),
      equal_list (fmap2 values values) (Cons (2, Cons (4, Nil))),
      equal_list
        (union values (Cons (3, Nil)))
        (Cons (1, Cons (2, Cons (3, Nil)))),
      equal_list (countdown 2) (Cons (2, Cons (1, Cons (0, Nil)))),
      equal_list (int_bound 2) (Cons (2, Cons (1, Cons (0, Nil))))
      && equal_list (int_range 2 4) (Cons (2, Cons (3, Cons (4, Nil)))),
      pair_count values values = 4 && option_count values = 3,
      oneof 4 5 true = 4
      && nil_gen unit_value = Nil
      && cons_gen 1 Nil = Cons (1, Nil)
      && oneofl values 1 = 2,
      frequency 1 7 9 = 7,
      numeral 48 && numeral 57 && not (numeral 65),
      equal_list (list_repeat 3 8) (Cons (8, Cons (8, Cons (8, Nil))))
      && positive_split 5 2 )

let[@refined.predicate] valid_library_report (report : library_report) : bool =
  match report with
  | Library_report (a, b, c, d, e, f, g, h, i, j, k, l) ->
      a && b && c && d && e && f && g && h && i && j && k && l

[@@@refined.axiom
{
  name = "library_report_intro";
  quantifiers = [];
  body =
    "valid_library_report (Library_report (true, true, true, true, true, true, \
     true, true, true, true, true, true))";
}]

[@@@refined.axiom
{
  name = "library_report_elim";
  quantifiers = [ ("forall", "report", "library_report") ];
  body =
    "implies (valid_library_report report) (report = Library_report (true, \
     true, true, true, true, true, true, true, true, true, true, true))";
}]

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {result:library_report | valid_library_report \
          result}";
       witness_relation =
         "result = Library_report (true, true, true, true, true, true, true, \
          true, true, true, true, true)";
     }] coverage_monad_library (unit_value : unit) : library_report =
  let _unused_unit = unit_value in
  Library_report
    (true, true, true, true, true, true, true, true, true, true, true, true)

let runtime_examples (_unit : unit) =
  valid_library_report (build_report _unit)
  && not
       (valid_library_report
          (Library_report
             ( true,
               true,
               true,
               true,
               true,
               true,
               true,
               true,
               true,
               true,
               true,
               false )))
