let[@refined.over { pre = "n >= 0"; post = "result = 0" }]
   [@refined.measure "n"] rec countdown (n : int) : int =
  if n = 0 then 0 else countdown (n - 1)
