exception Negative

let[@refined.over
     { pre = "true"; post = "true"; raises = [ ("Negative", "x >= 0") ] }] wrong_exception_post
    (x : int) : int =
  if x < 0 then raise Negative else x

let[@refined.over { pre = "true"; post = "true" }] unlisted (x : int) : int =
  if x < 0 then raise Negative else x
