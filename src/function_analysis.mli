type t = {
  dependency_graph : (string * string list) list;
  strongly_connected_components : string list list;
}

val analyze : Typed_core.program -> t
val is_recursive_edge : t -> caller:string -> callee:string -> bool
val is_recursive_function : t -> string -> bool
