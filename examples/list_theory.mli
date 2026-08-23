val mem : 'a list -> 'a -> bool [@@refined.predicate]
val hd : 'a list -> 'a -> bool [@@refined.predicate]

[@@@refined.axiom
{
  name = "hd_mem";
  vars = [ ("l", "'a list"); ("x", "'a") ];
  body = "implies (hd l x) (mem l x)";
}]
