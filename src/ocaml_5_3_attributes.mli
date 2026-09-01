open Refined_ir

val generic_scheme_of_attribute :
  Parsetree.attribute -> Generic_refinement.scheme option

val expression_refinement :
  Parsetree.attributes -> Generic_refinement.type_ option
