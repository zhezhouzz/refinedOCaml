let imported = Slicing_theory.touch

let[@refined.over
     {
       type_ =
         "x:{x:int | not (Slicing_theory.q x)} -> {result:int | not \
          (Slicing_theory.p x)}";
     }] use_left (x : int) : int =
  if Slicing_theory.p x then x else x

let[@refined.over
     {
       type_ =
         "x:{x:int | Slicing_theory.s x = false} -> {result:int | \
          Slicing_theory.r x = false}";
     }] use_right (x : int) : int =
  if Slicing_theory.r x then x else x

let[@refined.over { type_ = "x:int -> {result:int | result = x}" }] identity
    (x : int) : int =
  x
