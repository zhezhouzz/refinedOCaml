let[@refined.over { type_ = "n:{n:int | n >= 0} -> {result:int | result = 0}" }] rec unmeasured
    (n : int) : int =
  if n = 0 then 0 else unmeasured (n - 1)
