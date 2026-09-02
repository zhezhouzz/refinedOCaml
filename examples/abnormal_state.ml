exception Bad of int

type _ Effect.t += Send : int -> int Effect.t

let[@refined.over
     {
       type_ = "cell:int ref -> x:int -> {result:int | false}";
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
       type_ = "cell:int ref -> x:int -> {result:int | false}";
       outcomes =
         [
           ("raise", "Bad", "payload < 0", [], "x = payload && old_cell = 0");
           ("perform", "Send", "payload >= 0", [], "x = payload && old_cell = 0");
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
     {
       type_ = "cell:int ref -> {result:int | result = 1}";
       state = [ ("cell", "value = 1") ];
     }]
   [@refined.coverage
     {
       type_ = "cell:int ref -> {result:int | result = 1}";
       state = [ ("cell", "value = 1") ];
       witness_relation = "old_cell = 0";
     }] catches_abnormal_state (cell : int ref) : int =
  try abnormal_write cell (-1) with Bad _payload -> !cell

let[@refined.over
     {
       type_ = "cell:int ref -> {result:int | result = 2}";
       state = [ ("cell", "value = 2") ];
     }]
   [@refined.coverage
     {
       type_ = "cell:int ref -> {result:int | result = 2}";
       state = [ ("cell", "value = 2") ];
       witness_relation = "old_cell = 0";
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
