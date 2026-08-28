let[@refined.over { pre = "x >= 0"; post = "result >= 0" }] abs (x : int) : int
    =
  if x >= 0 then x else -x

let[@refined.over { pre = "n >= 0"; post = "result = 0" }]
   [@refined.measure "n"] rec countdown (n : int) : int =
  if n = 0 then 0 else countdown (n - 1)

let () =
  assert (abs (-2) = 2);
  assert (countdown 2 = 0)
