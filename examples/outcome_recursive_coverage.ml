exception Done of int

let[@refined.coverage
     {
       pre = "n >= 0";
       post = "false";
       outcomes = [ ("raise", "Done", "payload = 0", [ ("n", "0") ]) ];
     }]
   [@refined.measure "n"] rec covers_done (n : int) : int =
  if n = 0 then raise (Done 0) else covers_done (n - 1)
