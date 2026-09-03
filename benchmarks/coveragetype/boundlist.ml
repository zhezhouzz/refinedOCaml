(* SPDX-License-Identifier: MIT
   Port of CoverageType data/PLDI23/basic/boundlist.ml at
   c158b803c1c50ad61829e4ae079710f9d6cca52a.

   The upstream generator rejects candidates below [floor].  A total OCaml
   function cannot expose that rejection outcome, so this port maps such a
   candidate to [floor].  Its successful output set is unchanged: every list
   of length [size] whose elements are at least [floor] is still generated. *)

type ilist = Nil | Cons of int * ilist

let rec ilength value =
  match value with Nil -> 0 | Cons (_, tail) -> 1 + ilength tail

let rec all_ge floor value =
  match value with
  | Nil -> true
  | Cons (head, tail) -> head >= floor && all_ge floor tail

let[@refined.predicate] bounded (value : ilist) (expected : int) (floor : int) :
    bool =
  ilength value = expected && all_ge floor value

let[@refined.logic] list_head (value : ilist) : int =
  match value with Nil -> 0 | Cons (head, _) -> head

let[@refined.logic] list_tail (value : ilist) : ilist =
  match value with Nil -> Nil | Cons (_, tail) -> tail

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

(* A one-marker choice is refinedOCaml's typed havoc source and models the
   upstream [int_gen ()]. *)
let[@refined.choose] int_gen (_unit : unit) : int = 0

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size >= 0} -> floor:int -> {result:ilist | bounded \
          result size floor}";
       universals = [ "size"; "floor" ];
     }]
   [@refined.measure "size"] rec bound_list_gen (size : int) (floor : int) :
    ilist =
  if size = 0 then Nil
  else
    let candidate = int_gen () in
    let head = if floor <= candidate then candidate else floor in
    Cons (head, bound_list_gen (size - 1) floor)
