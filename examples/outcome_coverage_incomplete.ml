exception Bad of int

let[@refined.coverage
     {
       pre = "true";
       post = "false";
       outcomes = [ ("raise", "Bad", "true", [ ("x", "payload") ]) ];
     }] incomplete (x : int) (_y : int) : int =
  raise (Bad x)
