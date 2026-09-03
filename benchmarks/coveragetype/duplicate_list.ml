(* SPDX-License-Identifier: MIT
   Port of CoverageType data/PLDI23/basic/duplicate_list.ml at
   c158b803c1c50ad61829e4ae079710f9d6cca52a. *)

type ilist = Nil | Cons of int * ilist

let rec ilength value =
  match value with Nil -> 0 | Cons (_, tail) -> 1 + ilength tail

let rec all_equal expected value =
  match value with
  | Nil -> true
  | Cons (head, tail) -> head = expected && all_equal expected tail

let[@refined.predicate] duplicates (value : ilist) (expected : int) (item : int)
    : bool =
  ilength value = expected && all_equal item value

let[@refined.logic] list_tail (value : ilist) : ilist =
  match value with Nil -> Nil | Cons (_, tail) -> tail

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

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> item:int -> {result:ilist | \
          duplicates result size item}";
       universals = [ "size"; "item" ];
     }]
   [@refined.measure "size"] rec duplicate_list_gen (size : int) (item : int) :
    ilist =
  if size = 0 then Nil else Cons (item, duplicate_list_gen (size - 1) item)
