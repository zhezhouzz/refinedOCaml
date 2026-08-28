let[@refined.coverage
     { pre = "x >= 0"; post = "result >= 1"; witnesses = [ ("x", "result") ] }] bad_successor
    (x : int) : int =
  x + 1
