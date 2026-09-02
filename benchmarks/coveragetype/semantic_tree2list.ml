(* SPDX-License-Identifier: MIT
   Executable model of data/monad/tree2list.ml. *)

type tree = Leaf | Node of int * tree * tree
type ilist = Nil | Cons of int * ilist
type tree2list_report = Tree2list_report of bool * bool

let rec tree_nodes value =
  match value with
  | Leaf -> 0
  | Node (_, left, right) -> 1 + tree_nodes left + tree_nodes right

let rec list_length value =
  match value with Nil -> 0 | Cons (_, tail) -> 1 + list_length tail

let rec append left right =
  match left with Nil -> right | Cons (head, tail) -> Cons (head, append tail right)

let rec flatten value =
  match value with
  | Leaf -> Nil
  | Node (key, left, right) -> Cons (key, append (flatten left) (flatten right))

let flatten_preserves_size value = list_length (flatten value) = tree_nodes value

let build_report (_unit : unit) =
  let sample = Node (4, Node (2, Leaf, Leaf), Node (7, Leaf, Leaf)) in
  Tree2list_report (flatten_preserves_size sample, list_length (flatten Leaf) = 0)

let[@refined.predicate] valid_tree2list_report (report : tree2list_report) :
    bool =
  match report with
  | Tree2list_report (flatten_ok, generator_ok) -> flatten_ok && generator_ok

[@@@refined.axiom
{
  name = "tree2list_report_intro";
  quantifiers = [];
  body = "valid_tree2list_report (Tree2list_report (true, true))";
}]

[@@@refined.axiom
{
  name = "tree2list_report_elim";
  quantifiers = [ ("forall", "report", "tree2list_report") ];
  body =
    "implies (valid_tree2list_report report) (report = Tree2list_report (true, \
     true))";
}]

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {result:tree2list_report | \
          valid_tree2list_report result}";
       witness_relation = "result = Tree2list_report (true, true)";
     }] tree2list (unit_value : unit) : tree2list_report =
  let _unused_unit = unit_value in
  Tree2list_report (true, true)

let runtime_examples (_unit : unit) =
  let sample = Node (1, Node (2, Leaf, Leaf), Node (3, Leaf, Leaf)) in
  flatten_preserves_size Leaf && flatten_preserves_size sample
  && list_length (flatten sample) = 3
  && not (list_length (Cons (1, Nil)) = tree_nodes sample)
