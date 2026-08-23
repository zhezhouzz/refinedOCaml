let mem _list _element = false
let hd _list _element = false

(* This implementation-only assumption must never cross the .mli/.rmi boundary. *)
[@@@refined.axiom
{
  name = "private_mem_hd";
  vars = [ ("l", "'a list"); ("x", "'a") ];
  body = "implies (mem l x) (hd l x)";
}]
