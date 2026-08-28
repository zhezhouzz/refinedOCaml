type t

val equal : t -> t -> bool [@@refined.predicate]

[@@@refined.axiom
{ name = "equal_refl"; vars = [ ("x", "t") ]; body = "equal x x" }]

module Core : sig
  val holds : t -> bool [@@refined.predicate]

  [@@@refined.axiom
  { name = "holds_all"; vars = [ ("x", "t") ]; body = "holds x" }]
end

module Alias = Core
