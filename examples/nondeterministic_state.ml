external choose : int -> int -> int = "refined_choose" [@@refined.choose]

exception Picked

type _ Effect.t += Signal : int Effect.t

let[@refined.over
     {
       type_ = "seed:int -> {result:int | result = 1 || result = 2}";
       state = [ ("cell", "value = result") ];
     }]
   [@refined.coverage
     {
       type_ = "seed:int -> {result:int | result = 1 || result = 2}";
       witnesses = [ ("seed", "0") ];
       state = [ ("cell", "value = result") ];
     }] nondeterministic_write (seed : int) : int =
  let cell = ref seed in
  choose
    (cell := 1;
     !cell)
    (cell := 2;
     !cell)

let[@refined.over
     {
       type_ = "seed:int -> {result:int | false}";
       raises = [ ("Picked", "true") ];
       performs = [ ("Signal", "true") ];
       outcome_state =
         [
           ("raise", "Picked", "cell", "value = 3");
           ("perform", "Signal", "cell", "value = 4");
         ];
     }]
   [@refined.coverage
     {
       type_ = "seed:int -> {result:int | false}";
       outcomes =
         [
           ("raise", "Picked", "true", [ ("seed", "0") ]);
           ("perform", "Signal", "true", [ ("seed", "0") ]);
         ];
       outcome_state =
         [
           ("raise", "Picked", "cell", "value = 3");
           ("perform", "Signal", "cell", "value = 4");
         ];
     }] nondeterministic_outcome (seed : int) : int =
  let cell = ref seed in
  choose
    (cell := 3;
     raise Picked)
    (cell := 4;
     Effect.perform Signal)
