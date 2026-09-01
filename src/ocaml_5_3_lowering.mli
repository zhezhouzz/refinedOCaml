open Refined_ir

val symbol_of_ident : ?display:string -> Ident.t -> Typed_core.symbol
val typed_sort_of_type : Types.type_expr -> Typed_core.sort
val new_typed_registry : unit -> Typed_core.registry
val typed_register_types : Typed_core.registry -> Typedtree.structure -> unit

val typed_function :
  Typed_core.registry ->
  Typedtree.value_binding ->
  Typed_core.function_def option
