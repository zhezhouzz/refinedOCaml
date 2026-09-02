exception Bad of int

type _ Effect.t += Send : int -> int Effect.t

let[@refined.coverage
     {
       type_ = "x:int -> {result:int | result > 0}";
       witnesses = [ ("x", "result") ];
       outcomes =
         [
           ("raise", "Bad", "payload < 0", [ ("x", "payload") ]);
           ("perform", "Send", "payload = 0", [ ("x", "payload") ]);
         ];
     }] outcome (x : int) : int =
  if x < 0 then raise (Bad x) else if x = 0 then Effect.perform (Send x) else x

let[@refined.coverage
     {
       type_ = "x:int -> {result:int | result > 1}";
       witnesses = [ ("x", "result - 1") ];
       outcomes =
         [
           ("raise", "Bad", "payload < 0", [ ("x", "payload") ]);
           ("perform", "Send", "payload = 0", [ ("x", "payload") ]);
         ];
     }] mapped_outcome (x : int) : int =
  outcome x + 1
