let[@refined.over { pre = "x >= 0"; post = "result >= 0" }] abs (x : int) : int
    =
  if x >= 0 then x else -x

let () = assert (abs (-2) = 2)
