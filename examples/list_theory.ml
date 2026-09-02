let mem _list _element = false
let hd _list _element = false
let complement value = value
let require_zero value = value
let horn_identity value = value

(* This implementation-only assumption must never cross the .mli/.rmi boundary. *)
[@@@refined.axiom
{
  name = "private_mem_hd";
  quantifiers = [ ("forall", "l", "'a list"); ("forall", "x", "'a") ];
  body = "implies (mem l x) (hd l x)";
}]
