let[@refined.over
     {
       type_ =
         "f:(y:{y:int | y >= 0} -> {r:int | r > y}) -> x:{x:int | x >= 0} -> \
          {result:int | result > x}";
     }] apply_positive (f : int -> int) (x : int) : int =
  f x

let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] use_local
    (x : int) : int =
  let offset = 1 in
  let increment = fun y -> y + offset in
  apply_positive increment x

let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] use_anonymous
    (x : int) : int =
  apply_positive (fun y -> y + 1) x

let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] bad_local
    (x : int) : int =
  let decrement = fun y -> y - 1 in
  apply_positive decrement x

let[@refined.over
     {
       type_ =
         "offset:{offset:int | offset > 0} -> y:int -> {result:int | result > \
          y}";
     }] make_local_adder (offset : int) : int -> int =
 fun y -> y + offset

let[@refined.over { type_ = "x:int -> {result:int | result > x}" }] apply_returned_local
    (x : int) : int =
  let increment = make_local_adder 1 in
  increment x
