exception Negative

let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] safe_local
    (x : int) : int =
  let increment_or_raise = fun y -> if y >= 0 then y + 1 else raise Negative in
  increment_or_raise x

let[@refined.over { type_ = "x:int -> {result:int | result > x}" }] unsafe_local
    (x : int) : int =
  let increment_or_raise = fun y -> if y >= 0 then y + 1 else raise Negative in
  increment_or_raise x
