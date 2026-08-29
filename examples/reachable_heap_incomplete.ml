let[@refined.over
     { pre = "true"; post = "true"; result_references = [ ("0", "value = x") ] }] incomplete_ownership
    (x : int) : int ref * bool ref =
  (ref x, ref true)
