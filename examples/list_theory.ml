let mem _list _element = false
let hd _list _element = false
let complement value = value
let require_zero value = value

(* This implementation-only assumption must never cross the .mli/.rmi boundary. *)
[@@@refined.axiom
{
  name = "private_mem_hd";
  vars = [ ("l", "'a list"); ("x", "'a") ];
  body = "implies (mem l x) (hd l x)";
}]
