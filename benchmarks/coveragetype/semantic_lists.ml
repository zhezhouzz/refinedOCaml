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
  name = "list_bounded_elim";
  quantifiers = [ ("forall", "value", "ilist"); ("forall", "bound", "int") ];
  body =
    "implies (bound >= 0 && list_bounded value bound) (value = Nil || (bound > \
     0 && value = Cons (list_head value, list_tail value) && list_bounded \
     (list_tail value) (bound - 1)))";
}]

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false
let[@refined.predicate] exact (v : ilist) (n : int) : bool = ilength v = n

[@@@refined.axiom
{
  name = "exact_elim";
  quantifiers = [ ("forall", "v", "ilist"); ("forall", "n", "int") ];
  body =
    "implies (exact v n) ((n = 0 && v = Nil) || (n > 0 && v = Cons (list_head \
     v, list_tail v) && exact (list_tail v) (n - 1)))";
}]

[@@@refined.axiom
{
  name = "sorted_exact";
  quantifiers = [ ("forall", "v", "ilist"); ("forall", "n", "int") ];
  body = "implies (sorted_sized v n) (exact v n)";
}]

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {r:ilist | exact r size}";
       universals = [ "size" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec list_exact (size : int) : ilist =
  if size = 0 then Nil
  else
    let tail = list_exact (size - 1) in
    Cons (int_gen (), tail)

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {r:ilist | sorted_sized r size}";
       universals = [ "size" ];
       witness_relation = "true";
     }] sortedlist_simpl (size : int) : ilist =
  if size = 0 then Nil
  else
    let tail = list_exact (size - 1) in
    Cons (int_gen (), tail)

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {r:ilist | unique_sized r size}";
       universals = [ "size" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec unique_list_port (size : int) : ilist =
  if size = 0 then Nil
  else
    let tail = unique_list_port (size - 1) in
    let x = int_gen () in
    if absent x tail then Cons (x, tail) else raise Reject

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> {r:ilist | list_bounded r bound}";
       universals = [ "bound" ];
       witness_relation = "true";
     }]
   [@refined.measure "bound"] rec sized_list_port (bound : int) : ilist =
  if bound = 0 then Nil
  else if bool_gen () then Nil
  else Cons (int_gen (), sized_list_port (bound - 1))

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> lower:int -> {r:ilist | \
          sorted_from_sized r size lower}";
       universals = [ "size"; "lower" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec sorted_list_port (size : int) (lower : int) :
    ilist =
  if size = 0 then Nil
  else
    let y = int_gen () in
    if lower <= y then Cons (y, sorted_list_port (size - 1) y) else raise Reject

let runtime_examples (_unit : unit) =
  ilength (sortedlist_simpl 4) = 4
  && sorted_from_sized (sorted_list_port 4 0) 4 0
  && list_bounded (sized_list_port 5) 5
  && unique_sized (unique_list_port 1) 1
  &&
    try
      ignore (unique_list_port 2);
      false
    with Reject -> true
