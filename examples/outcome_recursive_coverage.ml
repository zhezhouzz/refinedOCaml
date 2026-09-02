exception Done of int

let[@refined.coverage
     {
       type_ = "n:{n:int | n >= 0} -> {result:int | false}";
       outcomes = [ ("raise", "Done", "payload = 0", [ ("n", "0") ]) ];
     }]
   [@refined.measure "n"] rec covers_done (n : int) : int =
  if n = 0 then raise (Done 0) else covers_done (n - 1)
