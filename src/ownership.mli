open Refined_ir

type returned_reference_path = {
  path : string;
  identity : string;
  content_sort : Typed_core.sort;
  guard : string;
}

val returned_reference_value_name : string -> string
val returned_reference_identity_name : string -> string
val result_reference_is_transfer : Typed_core.contract -> string -> bool

val validate_result_reference_permissions :
  loc:Source_span.t -> Typed_core.contract -> string list -> unit

val sort_reaches_reference : Typed_core.registry -> Typed_core.sort -> bool

val returned_reference_paths :
  ?recursive_frontier:bool ->
  Typed_core.registry ->
  result_sort:Typed_core.sort ->
  result:string ->
  (returned_reference_path list, string) result

val use_returned_reference_theory :
  (string -> unit) -> Typed_core.registry -> Typed_core.sort -> unit

val validate_region_contracts :
  Typed_core.program -> Typed_core.function_def -> Typed_core.contract -> unit

val region_frontier_specs :
  Typed_core.program ->
  Refined_types.mode ->
  loc:Source_span.t ->
  string ->
  root_sort:Typed_core.sort ->
  root:string ->
  (returned_reference_path * string * Source_span.t) list
