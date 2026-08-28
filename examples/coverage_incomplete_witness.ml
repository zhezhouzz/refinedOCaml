let[@refined.coverage
     { pre = "true"; post = "true"; witnesses = [ ("x", "result") ] }] incomplete
    (x : int) (_y : int) : int =
  x
