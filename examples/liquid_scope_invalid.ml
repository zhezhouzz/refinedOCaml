let[@refined.over { type_ = "x:{v:int | v >= y} -> y:int -> int" }] bad_scope
    (x : int) (y : int) : int =
  x + y
