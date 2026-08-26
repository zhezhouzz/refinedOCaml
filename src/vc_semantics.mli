type declaration = string * string

type context = {
  buffer : Buffer.t;
  arguments : declaration list;
  choices : declaration list;
  result_sort : string;
  body : string;
  pre : string;
  post : string;
  side_conditions : string list;
}

module type S = sig
  val mode : Refined_types.mode
  val encode : context -> unit
end

module Safety : S
module Coverage : S

val encode : Refined_types.mode -> context -> unit
