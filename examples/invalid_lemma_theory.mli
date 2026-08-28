val p : int -> bool [@@refined.predicate]
val q : int -> bool [@@refined.predicate]

[@@@refined.lemma
{
  name = "invented_implication";
  vars = [ ("x", "int") ];
  body = "implies (p x) (q x)";
}]
