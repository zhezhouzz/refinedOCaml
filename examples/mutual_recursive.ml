let[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> {result:bool | result = true || result = false}";
     }]
   [@refined.measure "n"] rec even (n : int) : bool =
  if n = 0 then true else odd (n - 1)

and[@refined.over
     {
       type_ =
         "n:{n:int | n >= 0} -> {result:bool | result = true || result = false}";
     }]
   [@refined.measure "n"] odd (n : int) : bool =
  if n = 0 then false else even (n - 1)
