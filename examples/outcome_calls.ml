exception Failed of int

type _ Effect.t += Send : int -> int Effect.t

let[@refined.over
     {
       pre = "true";
       post = "result = x";
       raises = [ ("Failed", "payload = x && x < 0") ];
       performs = [ ("Send", "payload = x && x = 0") ];
     }] outcome (x : int) : int =
  if x < 0 then raise (Failed x)
  else if x = 0 then Effect.perform (Send x)
  else x

let[@refined.over
     {
       pre = "true";
       post = "result = x";
       performs = [ ("Send", "payload = 0") ];
     }] catches_call (x : int) : int =
  try outcome x with Failed payload -> payload

let[@refined.over
     {
       pre = "true";
       post = "result = x";
       raises = [ ("Failed", "payload = x && x < 0") ];
     }] handles_call (x : int) : int =
  Effect.Deep.match_with
    (fun () -> outcome x)
    ()
    {
      retc = (fun value -> value);
      exnc = raise;
      effc =
        (fun (type result) (operation : result Effect.t) ->
          match operation with
          | Send payload ->
              Some
                (fun (continuation : (result, int) Effect.Deep.continuation) ->
                  Effect.Deep.continue continuation payload)
          | _ -> None);
    }
