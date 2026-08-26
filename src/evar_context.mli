module type TERM = sig
  type t
  type head

  val view : t -> [ `Variable of string | `Node of head * t list ]
  val make_node : head -> t list -> t
  val equal_head : head -> head -> bool
  val equal : t -> t -> bool
end

module Make (Term : TERM) : sig
  type context
  type error = Occurs of string * Term.t | Shape_mismatch of Term.t * Term.t

  val create : unit -> context
  val unify : context -> formal:Term.t -> actual:Term.t -> (unit, error) result
  val substitute : context -> Term.t -> Term.t
  val solution : context -> string -> Term.t option
  val has_solutions : context -> bool
  val is_complete : context -> variables:string list -> bool
end
