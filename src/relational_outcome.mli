type state = (string * string) list

type outcome =
  | Return of string
  | Raised of { exception_ : string; payload : string option }
  | Performed of {
      operation : string;
      payload : string option;
      continuation : string option;
    }

type path = {
  guard : string;
  initial_state : state;
  final_state : state;
  outcome : outcome;
}

type t = path list

val return : state:state -> string -> t
val raise_ : ?payload:string -> state:state -> string -> t

val perform :
  ?payload:string ->
  ?continuation:string ->
  state:state ->
  operation:string ->
  unit ->
  t

val read : state:state -> cell:string -> t
val write : state:state -> cell:string -> value:string -> t
val branch : condition:string -> if_true:t -> if_false:t -> t
val bind : t -> (string -> state -> t) -> t

val try_with :
  t -> (exception_:string -> payload:string option -> state:state -> t) -> t

val handle_effect :
  operation:string ->
  t ->
  (payload:string option -> continuation:string option -> state:state -> t) ->
  t

val safety_obligation :
  pre:string ->
  normal:(value:string -> initial:state -> final:state -> string) ->
  raised:
    (exception_:string ->
    payload:string option ->
    initial:state ->
    final:state ->
    string) ->
  performed:
    (operation:string ->
    payload:string option ->
    continuation:string option ->
    initial:state ->
    final:state ->
    string) ->
  t ->
  string

val coverage_obligation :
  target:string -> matches:(path -> string) -> t -> string
