exception Bad of int

let[@refined.coverage
     {
       pre = "true";
       post = "false";
       outcomes = [ ("raise", "Bad", "payload < 0", [ ("x", "payload + 1") ]) ];
     }] wrong_inverse (x : int) : int =
  if x < 0 then raise (Bad x) else x
