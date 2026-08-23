external choose : int -> int -> int = "refined_choose" [@@refined.choose]

let[@refined.over { pre = "true"; post = "result = 0 || result = 1" }]
   [@refined.coverage { pre = "true"; post = "result = 0 || result = 1" }] bit
    (_unit : unit) : int =
  0
