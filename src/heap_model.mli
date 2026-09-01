open Refined_ir

type state = (string * string) list

val heap_key : Typed_core.sort -> string
val initial_heap_name : Typed_core.sort -> string
val reference_sort : Typed_core.sort -> Typed_core.sort
val heap_select : state -> string -> Typed_core.sort -> string
val heap_store : state -> string -> Typed_core.sort -> string -> state

val heap_store_guarded :
  state -> string -> string -> Typed_core.sort -> string -> state

val alias_consistency : (string * Typed_core.sort * string) list -> string list

val guarded_alias_consistency :
  (string * Typed_core.sort * string * string) list -> string list

val guarded_identity_distinctness :
  (string * Typed_core.sort * string) list -> string list

val frame_obligations :
  initial:state ->
  final:state ->
  references:(string * string * Typed_core.sort) list ->
  modified:string list ->
  string list

val reference_modified_identities :
  (string * string * Typed_core.sort) list -> string list -> string list
