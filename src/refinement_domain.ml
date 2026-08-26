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

module Smt = struct
  type predicate = string
  type constraint_ = string

  let apply name arguments = "(" ^ String.concat " " (name :: arguments) ^ ")"
  let truth = "true"
  let falsity = "false"

  let conjunction = function
    | [] -> truth
    | [ predicate_ ] -> predicate_
    | predicates -> apply "and" predicates

  let disjunction = function
    | [] -> falsity
    | [ predicate_ ] -> predicate_
    | predicates -> apply "or" predicates

  let negate predicate = apply "not" [ predicate ]
  let implies antecedent consequent = apply "=>" [ antecedent; consequent ]
  let equality left right = apply "=" [ left; right ]

  let binders declarations =
    "("
    ^ String.concat " "
        (List.map
           (fun (name, sort) -> Printf.sprintf "(%s %s)" name sort)
           declarations)
    ^ ")"

  let forall declarations constraint_ =
    if declarations = [] then constraint_
    else apply "forall" [ binders declarations; constraint_ ]

  let exists declarations predicate =
    if declarations = [] then predicate
    else apply "exists" [ binders declarations; predicate ]

  let render_predicate predicate = predicate
  let render_constraint constraint_ = constraint_
end
