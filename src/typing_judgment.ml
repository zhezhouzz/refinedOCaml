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
         and type constraint_ = Domain.constraint_) =
struct
  module Domain = Domain
  module Denotation = Denotation

  type judgment = {
    predicate : Domain.predicate;
    constraints : Domain.constraint_ list;
    derivation : rule list;
  }

  type checked = { obligation : Domain.constraint_ }

  let synthesize ~rule ~predicate ~children =
    {
      predicate;
      constraints = List.concat_map (fun child -> child.constraints) children;
      derivation =
        rule :: List.concat_map (fun child -> child.derivation) children;
    }

  let branch ~guard ~if_true ~if_false =
    let predicate =
      Domain.disjunction
        [
          Domain.conjunction [ guard; if_true.predicate ];
          Domain.conjunction [ Domain.negate guard; if_false.predicate ];
        ]
    in
    synthesize ~rule:Branch ~predicate ~children:[ if_true; if_false ]

  let check ~assumptions ~expected judgment =
    {
      obligation =
        Denotation.subsume ~assumptions ~actual:judgment.predicate ~expected;
    }

  let predicate judgment = judgment.predicate
  let constraints judgment = judgment.constraints
  let derivation judgment = judgment.derivation
  let obligation checked = checked.obligation
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

module Safety_denotation = struct
  type predicate = string
  type constraint_ = string

  let mode = Refined_types.Over

  let subsume ~assumptions ~actual ~expected =
    Refinement_domain.Smt.implies
      (Refinement_domain.Smt.conjunction (assumptions @ [ actual ]))
      expected
end

module Coverage_denotation = struct
  type predicate = string
  type constraint_ = string

  let mode = Refined_types.Under

  let subsume ~assumptions ~actual ~expected =
    let actual = Refinement_domain.Smt.conjunction (assumptions @ [ actual ]) in
    Refinement_domain.Smt.implies expected actual
end

module Safety = Make (Refinement_domain.Smt) (Safety_denotation)
module Coverage = Make (Refinement_domain.Smt) (Coverage_denotation)
