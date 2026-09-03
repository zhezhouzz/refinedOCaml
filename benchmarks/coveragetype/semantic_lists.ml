(* SPDX-License-Identifier: MIT
   Semantic ports of the list generators recorded in
   ../manifest.tsv. The executable predicates are used by the runtime
   examples; the axioms expose the same one-constructor decomposition to the
   refinement solver. *)

type ilist = Nil | Cons of int * ilist
type list_case = List_case of int * int * ilist

let rec ilength value =
  match value with Nil -> 0 | Cons (_, tail) -> 1 + ilength tail

let rec all_ge floor value =
  match value with
  | Nil -> true
  | Cons (head, tail) -> head >= floor && all_ge floor tail

let rec all_equal expected value =
  match value with
  | Nil -> true
  | Cons (head, tail) -> head = expected && all_equal expected tail

let rec sorted_from lower value =
  match value with
  | Nil -> true
  | Cons (head, tail) -> head >= lower && sorted_from head tail

let sorted value =
  match value with Nil -> true | Cons (head, tail) -> sorted_from head tail

let rec member needle value =
  match value with
  | Nil -> false
  | Cons (head, tail) -> head = needle || member needle tail

let rec unique value =
  match value with
  | Nil -> true
  | Cons (head, tail) -> (not (member head tail)) && unique tail

let[@refined.predicate] bounded (value : ilist) (expected : int) (floor : int) :
    bool =
  ilength value = expected && all_ge floor value

let[@refined.predicate] duplicates (value : ilist) (expected : int) (item : int)
    : bool =
  ilength value = expected && all_equal item value

let[@refined.predicate] sorted_sized (value : ilist) (expected : int) : bool =
  ilength value = expected && sorted value

let[@refined.predicate] sorted_from_sized (value : ilist) (expected : int)
    (lower : int) : bool =
  ilength value = expected && sorted_from lower value

let[@refined.predicate] unique_sized (value : ilist) (expected : int) : bool =
  ilength value = expected && unique value

let[@refined.predicate] list_bounded (value : ilist) (bound : int) : bool =
  ilength value <= bound

let[@refined.predicate] absent (item : int) (value : ilist) : bool =
  not (member item value)

let[@refined.predicate] valid_bound_case (case : list_case) : bool =
  match case with List_case (size, floor, value) -> bounded value size floor

let[@refined.predicate] valid_duplicate_case (case : list_case) : bool =
  match case with List_case (size, item, value) -> duplicates value size item

let[@refined.predicate] valid_sorted_case (case : list_case) : bool =
  match case with
  | List_case (size, tag, value) -> tag = 0 && sorted_sized value size

let[@refined.predicate] valid_unique_case (case : list_case) : bool =
  match case with
  | List_case (size, tag, value) -> tag = 0 && unique_sized value size

let[@refined.predicate] valid_sized_case (case : list_case) : bool =
  match case with
  | List_case (bound, tag, value) ->
      tag = 0 && bound >= 0 && list_bounded value bound

let[@refined.predicate] valid_sorted_from_case (case : list_case) : bool =
  match case with
  | List_case (size, lower, value) -> sorted_from_sized value size lower

let[@refined.logic] list_head (value : ilist) : int =
  match value with Nil -> 0 | Cons (head, _) -> head

let[@refined.logic] list_tail (value : ilist) : ilist =
  match value with Nil -> Nil | Cons (_, tail) -> tail

let[@refined.logic] case_first (case : list_case) : int =
  match case with List_case (first, _, _) -> first

let[@refined.logic] case_second (case : list_case) : int =
  match case with List_case (_, second, _) -> second

let[@refined.logic] case_list (case : list_case) : ilist =
  match case with List_case (_, _, value) -> value

[@@@refined.axiom
{
  name = "bounded_nil";
  quantifiers = [ ("forall", "floor", "int") ];
  body = "bounded Nil 0 floor";
}]

[@@@refined.axiom
{
  name = "bounded_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "ilist");
      ("forall", "tail_size", "int");
      ("forall", "floor", "int");
    ];
  body =
    "implies (bounded tail tail_size floor && head >= floor) (bounded (Cons \
     (head, tail)) (tail_size + 1) floor)";
}]

[@@@refined.axiom
{
  name = "bounded_elim";
  quantifiers =
    [
      ("forall", "value", "ilist");
      ("forall", "expected", "int");
      ("forall", "floor", "int");
    ];
  body =
    "implies (bounded value expected floor) ((expected = 0 && value = Nil) || \
     (expected > 0 && value = Cons (list_head value, list_tail value) && \
     list_head value >= floor && bounded (list_tail value) (expected - 1) \
     floor))";
}]

[@@@refined.axiom
{
  name = "duplicates_nil";
  quantifiers = [ ("forall", "item", "int") ];
  body = "duplicates Nil 0 item";
}]

[@@@refined.axiom
{
  name = "duplicates_cons_intro";
  quantifiers =
    [
      ("forall", "item", "int");
      ("forall", "tail", "ilist");
      ("forall", "tail_size", "int");
    ];
  body =
    "implies (duplicates tail tail_size item) (duplicates (Cons (item, tail)) \
     (tail_size + 1) item)";
}]

[@@@refined.axiom
{
  name = "duplicates_elim";
  quantifiers =
    [
      ("forall", "value", "ilist");
      ("forall", "expected", "int");
      ("forall", "item", "int");
    ];
  body =
    "implies (duplicates value expected item) ((expected = 0 && value = Nil) \
     || (expected > 0 && value = Cons (item, list_tail value) && duplicates \
     (list_tail value) (expected - 1) item))";
}]

[@@@refined.axiom
{ name = "sorted_sized_nil"; quantifiers = []; body = "sorted_sized Nil 0" }]

[@@@refined.axiom
{
  name = "sorted_sized_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "ilist");
      ("forall", "tail_size", "int");
    ];
  body =
    "implies (sorted_from_sized tail tail_size head) (sorted_sized (Cons \
     (head, tail)) (tail_size + 1))";
}]

[@@@refined.axiom
{
  name = "sorted_sized_elim";
  quantifiers = [ ("forall", "value", "ilist"); ("forall", "expected", "int") ];
  body =
    "implies (sorted_sized value expected) ((expected = 0 && value = Nil) || \
     (expected > 0 && value = Cons (list_head value, list_tail value) && \
     sorted_from_sized (list_tail value) (expected - 1) (list_head value)))";
}]

[@@@refined.axiom
{
  name = "sorted_from_nil";
  quantifiers = [ ("forall", "lower", "int") ];
  body = "sorted_from_sized Nil 0 lower";
}]

[@@@refined.axiom
{
  name = "sorted_from_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "ilist");
      ("forall", "tail_size", "int");
      ("forall", "lower", "int");
    ];
  body =
    "implies (head >= lower && sorted_from_sized tail tail_size head) \
     (sorted_from_sized (Cons (head, tail)) (tail_size + 1) lower)";
}]

[@@@refined.axiom
{
  name = "sorted_from_elim";
  quantifiers =
    [
      ("forall", "value", "ilist");
      ("forall", "expected", "int");
      ("forall", "lower", "int");
    ];
  body =
    "implies (sorted_from_sized value expected lower) ((expected = 0 && value \
     = Nil) || (expected > 0 && value = Cons (list_head value, list_tail \
     value) && list_head value >= lower && sorted_from_sized (list_tail value) \
     (expected - 1) (list_head value)))";
}]

[@@@refined.axiom
{ name = "unique_nil"; quantifiers = []; body = "unique_sized Nil 0" }]

[@@@refined.axiom
{
  name = "unique_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "ilist");
      ("forall", "tail_size", "int");
    ];
  body =
    "implies (unique_sized tail tail_size && absent head tail) (unique_sized \
     (Cons (head, tail)) (tail_size + 1))";
}]

[@@@refined.axiom
{
  name = "unique_elim";
  quantifiers = [ ("forall", "value", "ilist"); ("forall", "expected", "int") ];
  body =
    "implies (unique_sized value expected) ((expected = 0 && value = Nil) || \
     (expected > 0 && value = Cons (list_head value, list_tail value) && \
     absent (list_head value) (list_tail value) && unique_sized (list_tail \
     value) (expected - 1)))";
}]

[@@@refined.axiom
{
  name = "list_bounded_nil";
  quantifiers = [ ("forall", "bound", "int") ];
  body = "implies (bound >= 0) (list_bounded Nil bound)";
}]

[@@@refined.axiom
{
  name = "list_bounded_cons_intro";
  quantifiers =
    [
      ("forall", "head", "int");
      ("forall", "tail", "ilist");
      ("forall", "bound", "int");
    ];
  body =
    "implies (bound > 0 && list_bounded tail (bound - 1)) (list_bounded (Cons \
     (head, tail)) bound)";
}]

[@@@refined.axiom
{
  name = "list_bounded_elim";
  quantifiers = [ ("forall", "value", "ilist"); ("forall", "bound", "int") ];
  body =
    "implies (bound >= 0 && list_bounded value bound) (value = Nil || (bound > \
     0 && value = Cons (list_head value, list_tail value) && list_bounded \
     (list_tail value) (bound - 1)))";
}]

[@@@refined.axiom
{
  name = "valid_bound_case_intro";
  quantifiers =
    [
      ("forall", "size", "int");
      ("forall", "floor", "int");
      ("forall", "value", "ilist");
    ];
  body =
    "implies (bounded value size floor) (valid_bound_case (List_case (size, \
     floor, value)))";
}]

[@@@refined.axiom
{
  name = "valid_bound_case_elim";
  quantifiers = [ ("forall", "case", "list_case") ];
  body =
    "implies (valid_bound_case case) (case = List_case (case_first case, \
     case_second case, case_list case) && bounded (case_list case) (case_first \
     case) (case_second case))";
}]

[@@@refined.axiom
{
  name = "valid_duplicate_case_intro";
  quantifiers =
    [
      ("forall", "size", "int");
      ("forall", "item", "int");
      ("forall", "value", "ilist");
    ];
  body =
    "implies (duplicates value size item) (valid_duplicate_case (List_case \
     (size, item, value)))";
}]

[@@@refined.axiom
{
  name = "valid_duplicate_case_elim";
  quantifiers = [ ("forall", "case", "list_case") ];
  body =
    "implies (valid_duplicate_case case) (case = List_case (case_first case, \
     case_second case, case_list case) && duplicates (case_list case) \
     (case_first case) (case_second case))";
}]

[@@@refined.axiom
{
  name = "valid_sorted_case_intro";
  quantifiers = [ ("forall", "size", "int"); ("forall", "value", "ilist") ];
  body =
    "implies (sorted_sized value size) (valid_sorted_case (List_case (size, 0, \
     value)))";
}]

[@@@refined.axiom
{
  name = "valid_sorted_case_elim";
  quantifiers = [ ("forall", "case", "list_case") ];
  body =
    "implies (valid_sorted_case case) (case = List_case (case_first case, 0, \
     case_list case) && case_second case = 0 && sorted_sized (case_list case) \
     (case_first case))";
}]

[@@@refined.axiom
{
  name = "valid_unique_case_intro";
  quantifiers = [ ("forall", "size", "int"); ("forall", "value", "ilist") ];
  body =
    "implies (unique_sized value size) (valid_unique_case (List_case (size, 0, \
     value)))";
}]

[@@@refined.axiom
{
  name = "valid_unique_case_elim";
  quantifiers = [ ("forall", "case", "list_case") ];
  body =
    "implies (valid_unique_case case) (case = List_case (case_first case, 0, \
     case_list case) && case_second case = 0 && unique_sized (case_list case) \
     (case_first case))";
}]

[@@@refined.axiom
{
  name = "valid_sized_case_intro";
  quantifiers = [ ("forall", "bound", "int"); ("forall", "value", "ilist") ];
  body =
    "implies (bound >= 0 && list_bounded value bound) (valid_sized_case \
     (List_case (bound, 0, value)))";
}]

[@@@refined.axiom
{
  name = "valid_sized_case_elim";
  quantifiers = [ ("forall", "case", "list_case") ];
  body =
    "implies (valid_sized_case case) (case = List_case (case_first case, 0, \
     case_list case) && case_second case = 0 && case_first case >= 0 && \
     list_bounded (case_list case) (case_first case))";
}]

[@@@refined.axiom
{
  name = "valid_sorted_from_case_intro";
  quantifiers =
    [
      ("forall", "size", "int");
      ("forall", "lower", "int");
      ("forall", "value", "ilist");
    ];
  body =
    "implies (sorted_from_sized value size lower) (valid_sorted_from_case \
     (List_case (size, lower, value)))";
}]

[@@@refined.axiom
{
  name = "valid_sorted_from_case_elim";
  quantifiers = [ ("forall", "case", "list_case") ];
  body =
    "implies (valid_sorted_from_case case) (case = List_case (case_first case, \
     case_second case, case_list case) && sorted_from_sized (case_list case) \
     (case_first case) (case_second case))";
}]

let[@refined.choose] choose_list (left : ilist) (_right : ilist) : ilist = left

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> head:int -> tail:ilist -> \
          {result:list_case | valid_sorted_case result}";
       witness_relation =
         "result = List_case (size, 0, case_list result) && ((size = 0 && \
          case_list result = Nil) || (size > 0 && case_list result = Cons \
          (head, tail) && sorted_from_sized tail (size - 1) head))";
     }] sortedlist_simpl (size : int) (head : int) (tail : ilist) : list_case =
  List_case (size, 0, choose_list Nil (Cons (head, tail)))

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> head:int -> tail:ilist -> \
          {result:list_case | valid_unique_case result}";
       witness_relation =
         "result = List_case (size, 0, case_list result) && ((size = 0 && \
          case_list result = Nil) || (size > 0 && case_list result = Cons \
          (head, tail) && absent head tail && unique_sized tail (size - 1)))";
     }] unique_list_port (size : int) (head : int) (tail : ilist) : list_case =
  List_case (size, 0, choose_list Nil (Cons (head, tail)))

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> head:int -> tail:ilist -> \
          {result:list_case | valid_sized_case result}";
       witness_relation =
         "result = List_case (bound, 0, case_list result) && (case_list result \
          = Nil || (bound > 0 && case_list result = Cons (head, tail) && \
          list_bounded tail (bound - 1)))";
     }] sized_list_port (bound : int) (head : int) (tail : ilist) : list_case =
  List_case (bound, 0, choose_list Nil (Cons (head, tail)))

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> lower:int -> head:int -> tail:ilist \
          -> {result:list_case | valid_sorted_from_case result}";
       witness_relation =
         "result = List_case (size, lower, case_list result) && ((size = 0 && \
          case_list result = Nil) || (size > 0 && case_list result = Cons \
          (head, tail) && head >= lower && sorted_from_sized tail (size - 1) \
          head))";
     }] sorted_list_port (size : int) (lower : int) (head : int) (tail : ilist)
    : list_case =
  List_case (size, lower, choose_list Nil (Cons (head, tail)))

let runtime_examples (_unit : unit) =
  let increasing = Cons (1, Cons (2, Cons (2, Nil))) in
  let decreasing = Cons (2, Cons (1, Nil)) in
  let repeated = Cons (7, Cons (7, Cons (7, Nil))) in
  let distinct = Cons (4, Cons (2, Cons (9, Nil))) in
  let duplicate = Cons (4, Cons (2, Cons (4, Nil))) in
  let two_items = Cons (10, Cons (20, Nil)) in
  bounded increasing 3 1
  && (not (bounded increasing 3 2))
  && duplicates repeated 3 7
  && (not (duplicates repeated 2 7))
  && sorted_sized increasing 3
  && (not (sorted_sized decreasing 2))
  && unique_sized distinct 3
  && (not (unique_sized duplicate 3))
  && list_bounded two_items 2
  && (not (list_bounded two_items 1))
  && sorted_from_sized increasing 3 0
  && not (sorted_from_sized increasing 3 2)
