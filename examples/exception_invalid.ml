exception Negative

let[@refined.over
     { type_ = "x:int -> int"; raises = [ ("Negative", "x >= 0") ] }] wrong_exception_post
    (x : int) : int =
  if x < 0 then raise Negative else x

let[@refined.over { type_ = "x:int -> int" }] unlisted (x : int) : int =
  if x < 0 then raise Negative else x
