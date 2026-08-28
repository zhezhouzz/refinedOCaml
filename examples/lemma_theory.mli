val p : int -> bool [@@refined.predicate]
val q : int -> bool [@@refined.predicate]

[@@@refined.axiom
{ name = "p_implies_q"; vars = [ ("x", "int") ]; body = "implies (p x) (q x)" }]

[@@@refined.lemma
{
  name = "not_q_implies_not_p";
  vars = [ ("x", "int") ];
  body = "implies (not (q x)) (not (p x))";
}]

[@@@refined.lemma
{
  name = "p_implies_q_checked";
  vars = [ ("x", "int") ];
  body = "implies (p x) (q x)";
}]
