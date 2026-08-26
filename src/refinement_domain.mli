module type S = sig
  type predicate
  type constraint_

  val truth : predicate
  val falsity : predicate
  val conjunction : predicate list -> predicate
  val disjunction : predicate list -> predicate
  val negate : predicate -> predicate
  val implies : predicate -> predicate -> constraint_
  val equality : string -> string -> predicate
  val forall : (string * string) list -> constraint_ -> constraint_
  val exists : (string * string) list -> predicate -> predicate
  val render_predicate : predicate -> string
  val render_constraint : constraint_ -> string
end

module Smt : S with type predicate = string and type constraint_ = string
