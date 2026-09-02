val p : int -> bool [@@refined.predicate]
val q : int -> bool [@@refined.predicate]
val r : int -> bool [@@refined.predicate]
val s : int -> bool [@@refined.predicate]
val touch : int

[@@@refined.axiom
{
  name = "p_implies_q";
  quantifiers = [ ("forall", "x", "int") ];
  body = "implies (p x) (q x)";
}]

[@@@refined.axiom
{
  name = "r_implies_s";
  quantifiers = [ ("forall", "x", "int") ];
  body = "implies (r x) (s x)";
}]

[@@@refined.lemma
{
  name = "not_q_implies_not_p";
  quantifiers = [ ("forall", "x", "int") ];
  body = "implies (not (q x)) (not (p x))";
}]

[@@@refined.lemma
{
  name = "not_s_implies_not_r";
  quantifiers = [ ("forall", "x", "int") ];
  body = "implies (not (s x)) (not (r x))";
}]
