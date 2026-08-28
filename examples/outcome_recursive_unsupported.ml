exception Stop of int

let[@refined.over
     { pre = "n >= 0"; post = "true"; raises = [ ("Stop", "payload = 0") ] }]
   [@refined.measure "n"] rec recursive_outcome (n : int) : int =
  if n = 0 then raise (Stop 0) else recursive_outcome (n - 1)
