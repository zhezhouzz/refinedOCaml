let[@refined.coverage
     {
       type_ = "f:(x:int -> {v:int | v = x}) -> x:int -> {v:int | v = x}";
       universals = [ "x" ];
     }] apply_identity (f : int -> int) (x : int) : int =
  f x
