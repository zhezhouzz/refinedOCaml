let[@refined.over { pre = "n >= 0"; post = "result = 0" }]
   [@refined.coverage { pre = "n >= 0"; post = "result = 0" }]
   [@refined.measure "n"] rec unsupported_coverage (n : int) : int =
  if n = 0 then 0 else unsupported_coverage (n - 1)
