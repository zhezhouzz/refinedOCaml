let[@refined.over { type_ = "n:{n:int | n >= 0} -> {result:int | result = 0}" }]
   [@refined.measure "n"] rec countdown (n : int) : int =
  if n = 0 then 0 else countdown (n - 1)
