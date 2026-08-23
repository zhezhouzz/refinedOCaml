val mem : 'a list -> 'a -> bool [@@refined.predicate]
val hd : 'a list -> 'a -> bool [@@refined.predicate]
val changed_api_marker : unit

[@@@refined.axiom
{
  name = "hd_mem";
  vars = [ ("l", "'a list"); ("x", "'a") ];
  body = "implies (hd l x) (mem l x)";
}]
