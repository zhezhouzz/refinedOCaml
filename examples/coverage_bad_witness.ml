let[@refined.coverage
     {
       type_ = "x:{x:int | x >= 0} -> {result:int | result >= 1}";
       witnesses = [ ("x", "result") ];
     }] bad_successor (x : int) : int =
  x + 1
