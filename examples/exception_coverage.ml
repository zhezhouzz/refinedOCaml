exception Negative

let[@refined.coverage { pre = "true"; post = "true" }] unsupported_exception
    (x : int) : int =
  if x < 0 then raise Negative else x
