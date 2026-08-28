exception Stop of int

let[@refined.over
     { pre = "n >= 0"; post = "true"; raises = [ ("Stop", "payload = 0") ] }] rec missing_measure
    (n : int) : int =
  if n = 0 then raise (Stop 0) else missing_measure (n - 1)
