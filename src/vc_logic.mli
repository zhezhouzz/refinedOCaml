open Refined_ir

module Sort_evars : sig
  type context

  type error =
    | Occurs of string * Typed_core.sort
    | Shape_mismatch of Typed_core.sort * Typed_core.sort

  val create : unit -> context

  val unify :
    context ->
    formal:Typed_core.sort ->
    actual:Typed_core.sort ->
    (unit, error) result

  val substitute : context -> Typed_core.sort -> Typed_core.sort
end

val typed_smt_sort : Typed_core.sort -> string
val reference_content_sort : Typed_core.sort -> Typed_core.sort option
val typed_constructor_name : Typed_core.constructor -> string
val typed_recognizer : Typed_core.constructor -> string
val typed_selector : Typed_core.constructor -> int -> string
val typed_tuple_constructor : Typed_core.sort -> string
val typed_tuple_selector : Typed_core.sort -> int -> string
val typed_logic_name : Typed_core.logic_symbol -> string

val typed_lookup_logic :
  Typed_core.registry -> string list -> string -> Typed_core.logic_symbol option

val typed_specialize_program :
  Typed_core.program ->
  Typed_core.function_def ->
  Parsetree.expression list ->
  Parsetree.expression ->
  Typed_core.program

val typed_monomorphize_datatypes :
  Typed_core.program -> Typed_core.function_def -> Typed_core.program

val typed_formula :
  ?scope:string list ->
  ?expected:Typed_core.sort ->
  Typed_core.registry ->
  (string * (string * Typed_core.sort)) list ->
  Parsetree.expression ->
  string

val formula_theory_symbols :
  ?scope:string list ->
  ?expected:Typed_core.sort ->
  Typed_core.registry ->
  (string * (string * Typed_core.sort)) list ->
  Parsetree.expression ->
  string list

val slice_program_theory :
  Typed_core.program -> roots:string list -> Typed_core.program * string list
