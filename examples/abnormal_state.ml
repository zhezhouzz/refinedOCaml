exception Bad of int

type _ Effect.t += Send : int -> int Effect.t

let[@refined.over
     {
       pre = "true";
       post = "false";
       raises = [ ("Bad", "payload = x && x < 0") ];
       performs = [ ("Send", "payload = x && x >= 0") ];
       outcome_state =
         [
           ("raise", "Bad", "cell", "value = 1");
           ("perform", "Send", "cell", "value = 2");
         ];
     }]
   [@refined.coverage
     {
       pre = "true";
       post = "false";
       state_witnesses = [ ("cell", "0") ];
       outcomes =
         [
           ("raise", "Bad", "payload < 0", [ ("x", "payload") ]);
           ("perform", "Send", "payload >= 0", [ ("x", "payload") ]);
         ];
       outcome_state =
         [
           ("raise", "Bad", "cell", "value = 1");
           ("perform", "Send", "cell", "value = 2");
         ];
     }] abnormal_write (cell : int ref) (x : int) : int =
  if x < 0 then (
    cell := 1;
    raise (Bad x))
  else (
    cell := 2;
    Effect.perform (Send x))

let[@refined.over
     { pre = "true"; post = "result = 1"; state = [ ("cell", "value = 1") ] }]
   [@refined.coverage
     {
       pre = "true";
       post = "result = 1";
       state = [ ("cell", "value = 1") ];
       state_witnesses = [ ("cell", "0") ];
     }] catches_abnormal_state (cell : int ref) : int =
  try abnormal_write cell (-1) with Bad _payload -> !cell

let[@refined.over
     { pre = "true"; post = "result = 2"; state = [ ("cell", "value = 2") ] }]
   [@refined.coverage
     {
       pre = "true";
       post = "result = 2";
       state = [ ("cell", "value = 2") ];
       state_witnesses = [ ("cell", "0") ];
     }] handles_abnormal_state (cell : int ref) : int =
  Effect.Deep.match_with
    (fun () -> abnormal_write cell 0)
    ()
    {
      retc = (fun value -> value);
      exnc = raise;
      effc =
        (fun (type result) (operation : result Effect.t) ->
          match operation with
          | Send _payload ->
              Some
                (fun (_continuation : (result, int) Effect.Deep.continuation) ->
                  !cell)
          | _ -> None);
    }
