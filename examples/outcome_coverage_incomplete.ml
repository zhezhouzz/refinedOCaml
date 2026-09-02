exception Bad of int

let[@refined.coverage
     {
       type_ = "x:int -> _y:int -> {result:int | false}";
       outcomes = [ ("raise", "Bad", "true", [ ("x", "payload") ]) ];
     }] incomplete (x : int) (_y : int) : int =
  raise (Bad x)
