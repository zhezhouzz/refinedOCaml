let[@refined.over { type_ = "z:{z:int | z >= 0} -> {w:int | w = z}" }] identity
    (z : int) : int =
  z

let[@refined.over
     {
       type_ =
         "f:(y:{y:int | y >= 0} -> {r:int | r > y}) -> x:{x:int | x >= 0} -> \
          {result:int | result > x}";
     }] apply_positive (f : int -> int) (x : int) : int =
  f x

let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] use_bad_callback
    (x : int) : int =
  apply_positive identity x
