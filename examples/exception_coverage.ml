exception Negative

let[@refined.coverage { type_ = "x:int -> int" }] unsupported_exception
    (x : int) : int =
  if x < 0 then raise Negative else x
