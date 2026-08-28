exception Negative
exception Other

let[@refined.over
     { pre = "true"; post = "result >= 0"; raises = [ ("Negative", "x < 0") ] }] classify
    (x : int) : int =
  if x < 0 then raise Negative else x

let[@refined.over { pre = "true"; post = "result >= 0" }] handled (x : int) :
    int =
  try if x < 0 then raise Negative else x with Negative -> 0

let[@refined.over { pre = "true"; post = "result = 1" }] catch_all (flag : bool)
    : int =
  try if flag then raise Negative else raise Other with _ -> 1
