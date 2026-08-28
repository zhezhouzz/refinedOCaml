module Arg1 = struct
  type t = int

  let enabled = true
end

module Arg2 = struct
  type t = bool

  let enabled = true
end

module Make (X : sig
  type t

  val enabled : bool
end) =
struct
  type t = int

  let mark _value = true
end

module Fresh () = struct
  type t = int

  let mark _value = true
end
