let[@refined.measure "n"] rec hidden_loop (n : int) : int =
  if n = 0 then 0 else hidden_loop (n - 1)

let[@refined.over { type_ = "n:{n:int | n >= 0} -> {result:int | result = 0}" }] expose_loop
    (n : int) : int =
  hidden_loop n
