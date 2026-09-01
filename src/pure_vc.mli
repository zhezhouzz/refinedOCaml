open Refined_ir

val typed_obligation :
  Typed_core.program ->
  Function_analysis.t ->
  Typed_core.function_def ->
  Typed_core.contract ->
  Refined_types.obligation
