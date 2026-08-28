let[@refined.over { pre = "n >= 0"; post = "result = 0" }]
   [@refined.measure "n"] rec stationary (n : int) : int =
  if n = 0 then 0 else stationary n
