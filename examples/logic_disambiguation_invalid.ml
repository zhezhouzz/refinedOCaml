type 'a box = Box of 'a

let[@refined.over
     { type_ = "x:int -> flag:bool -> {result:int box | result = Box flag}" }] wrong_box
    (x : int) (flag : bool) : int box =
  Box x
