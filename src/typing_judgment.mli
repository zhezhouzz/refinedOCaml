type rule =
  | Variable
  | Constant
  | Primitive
  | Application
  | Abstraction
  | Let
  | Branch
  | Match
  | Constructor
  | Projection
  | Choice
  | Function_body

module type DENOTATION = sig
  type predicate
  type constraint_

  val mode : Refined_types.mode

  val subsume :
    assumptions:predicate list ->
    actual:predicate ->
    expected:predicate ->
    constraint_
end

module Make
    (Domain : Refinement_domain.S)
    (Denotation :
      DENOTATION
        with type predicate = Domain.predicate
         and type constraint_ = Domain.constraint_) : sig
  module Domain : module type of Domain
  module Denotation : module type of Denotation

  type judgment
  type checked

  val synthesize :
    rule:rule ->
    predicate:Domain.predicate ->
    children:judgment list ->
    judgment

  val branch :
    guard:Domain.predicate -> if_true:judgment -> if_false:judgment -> judgment

  val check :
    assumptions:Domain.predicate list ->
    expected:Domain.predicate ->
    judgment ->
    checked

  val predicate : judgment -> Domain.predicate
  val constraints : judgment -> Domain.constraint_ list
  val derivation : judgment -> rule list
  val obligation : checked -> Domain.constraint_
end

module type STRING_JUDGMENT = sig
  type judgment
  type checked

  val synthesize :
    rule:rule -> predicate:string -> children:judgment list -> judgment

  val branch : guard:string -> if_true:judgment -> if_false:judgment -> judgment
  val check : assumptions:string list -> expected:string -> judgment -> checked
  val predicate : judgment -> string
  val constraints : judgment -> string list
  val derivation : judgment -> rule list
  val obligation : checked -> string
end

module Safety : STRING_JUDGMENT
module Coverage : STRING_JUDGMENT
