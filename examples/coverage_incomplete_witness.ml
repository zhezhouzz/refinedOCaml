let[@refined.coverage
     { type_ = "x:int -> _y:int -> int"; witnesses = [ ("x", "result") ] }] incomplete
    (x : int) (_y : int) : int =
  x
