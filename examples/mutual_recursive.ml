let[@refined.over { pre = "n >= 0"; post = "result = true || result = false" }]
   [@refined.measure "n"] rec even (n : int) : bool =
  if n = 0 then true else odd (n - 1)

and[@refined.over { pre = "n >= 0"; post = "result = true || result = false" }]
   [@refined.measure "n"] odd (n : int) : bool =
  if n = 0 then false else even (n - 1)
