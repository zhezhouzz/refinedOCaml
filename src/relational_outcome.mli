type state = (string * string) list

type outcome =
  | Return of string
  | Raised of string
  | Performed of { operation : string; payload : string }

type path = {
  guard : string;
  initial_state : state;
  final_state : state;
  outcome : outcome;
}

type t = path list

val return : state:state -> string -> t
val raise_ : state:state -> string -> t
val perform : state:state -> operation:string -> payload:string -> t
val read : state:state -> cell:string -> t
val write : state:state -> cell:string -> value:string -> t
val branch : condition:string -> if_true:t -> if_false:t -> t
val bind : t -> (string -> state -> t) -> t
val try_with : t -> (string -> state -> t) -> t

val handle_effect :
  operation:string -> t -> (payload:string -> state:state -> t) -> t

val safety_obligation :
  pre:string ->
  normal:(value:string -> initial:state -> final:state -> string) ->
  raised:(exception_:string -> initial:state -> final:state -> string) ->
  performed:
    (operation:string ->
    payload:string ->
    initial:state ->
    final:state ->
    string) ->
  t ->
  string

val coverage_obligation :
  target:string -> matches:(path -> string) -> t -> string
