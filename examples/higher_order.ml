let[@refined.over
     {
       type_ =
         "f:(y:{y:int | y >= 0} -> {r:int | r > y}) -> x:{x:int | x >= 0} -> \
          {result:int | result > x}";
     }] apply_positive (f : int -> int) (x : int) : int =
  f x

let[@refined.over
     {
       type_ =
         "f:(y:{y:int | y >= 0} -> {r:int | r > y}) -> x:{x:int | x >= 0} -> \
          {result:int | result > x}";
     }] bad_apply_positive (f : int -> int) (x : int) : int =
  f (x - 1)

let[@refined.over { type_ = "z:{z:int | z >= 0} -> {w:int | w > z}" }] increment
    (z : int) : int =
  z + 1

let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] use_increment
    (x : int) : int =
  apply_positive increment x
