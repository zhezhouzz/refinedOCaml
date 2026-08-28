let imported = Slicing_theory.touch

let[@refined.over
     { pre = "not (Slicing_theory.q x)"; post = "not (Slicing_theory.p x)" }] use_left
    (x : int) : int =
  if Slicing_theory.p x then x else x

let[@refined.over
     { pre = "Slicing_theory.s x = false"; post = "Slicing_theory.r x = false" }] use_right
    (x : int) : int =
  if Slicing_theory.r x then x else x

let[@refined.over { pre = "true"; post = "result = x" }] identity (x : int) :
    int =
  x
