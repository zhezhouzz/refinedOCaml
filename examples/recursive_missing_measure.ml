let[@refined.over { pre = "n >= 0"; post = "result = 0" }] rec unmeasured
    (n : int) : int =
  if n = 0 then 0 else unmeasured (n - 1)
