module Arg1 : sig
  type t

  val enabled : bool [@@refined.predicate]

  [@@@refined.axiom { name = "enabled"; vars = []; body = "enabled" }]
end

module Fresh () : sig
  type t

  val mark : t -> bool [@@refined.predicate]

  [@@@refined.axiom
  { name = "mark_all"; vars = [ ("x", "t") ]; body = "mark x" }]
end

module Arg2 : sig
  type t

  val enabled : bool [@@refined.predicate]

  [@@@refined.axiom { name = "enabled"; vars = []; body = "enabled" }]
end

module Make (X : sig
  type t

  val enabled : bool [@@refined.predicate]
end) : sig
  type t

  val mark : t -> bool [@@refined.predicate]

  [@@@refined.axiom
  {
    name = "mark_enabled";
    vars = [ ("x", "t") ];
    body = "implies X.enabled (mark x)";
  }]
end
