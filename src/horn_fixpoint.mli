module type TERM = sig
  type t
  type parameter

  val falsity : t
  val join : t list -> t
  val lambda : parameter:parameter -> t -> t
  val instantiate : (string * t) list -> t -> t
  val abstract : argument:t -> parameter:parameter -> t -> t
  val dependencies : variables:string list -> t -> string list
  val equal : t -> t -> bool
end

module Make (Term : TERM) : sig
  type variable = { name : string; parameter : Term.parameter }
  type clause = { head : string; argument : Term.t; body : Term.t }

  type solution = {
    predicates : (string * Term.t) list;
    dependency_graph : (string * string list) list;
    strongly_connected_components : string list list;
    iterations : int;
  }

  type error = Did_not_converge of int

  val solve :
    ?max_iterations:int ->
    variables:variable list ->
    clauses:clause list ->
    unit ->
    (solution, error) result
end
