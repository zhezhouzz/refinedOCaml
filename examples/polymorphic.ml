type 'a box = Box of 'a

let id value = value

let[@refined.over { type_ = "x:int -> {result:int | result = x}" }] use_int
    (x : int) : int =
  id x

let[@refined.over { type_ = "x:bool -> {result:bool | result = x}" }] use_bool
    (x : bool) : bool =
  id x
