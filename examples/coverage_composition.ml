let[@refined.coverage
     {
       type_ = "x:{x:int | x >= 0} -> {result:int | result >= 1}";
       witnesses = [ ("x", "result - 1") ];
     }] successor (x : int) : int =
  x + 1

let[@refined.coverage
     {
       type_ = "x:{x:int | x >= 0} -> {result:int | result >= 2}";
       witnesses = [ ("x", "result - 2") ];
     }] successor_twice (x : int) : int =
  successor (successor x)

let[@refined.coverage
     {
       type_ = "n:{n:int | n >= 0} -> {result:int | result = 0}";
       witnesses = [ ("n", "0") ];
     }]
   [@refined.measure "n"] rec countdown (n : int) : int =
  if n = 0 then 0 else countdown (n - 1)
