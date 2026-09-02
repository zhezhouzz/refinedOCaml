let[@refined.over { type_ = "x:int -> y:int -> {result:int | result = x + y}" }] add
    (x : int) (y : int) : int =
  x + y

let[@refined.over { type_ = "x:int -> y:int -> {result:int | result = x + y}" }] make_adder
    (x : int) : int -> int =
  add x

let[@refined.over { type_ = "x:int -> y:int -> {result:int | result = x + y}" }] use_adder
    (x : int) (y : int) : int =
  let adder = make_adder x in
  adder y

let[@refined.over { type_ = "x:int -> y:int -> {result:int | result = x + y}" }] bad_make_adder
    (x : int) : int -> int =
  add (x + 1)
