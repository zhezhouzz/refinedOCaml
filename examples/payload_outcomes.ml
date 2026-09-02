exception Bad of int

type _ Effect.t += Send : int -> int Effect.t

let[@refined.over
     {
       type_ = "x:int -> {result:int | result = x}";
       raises = [ ("Bad", "payload = x") ];
     }] payload_raise (x : int) : int =
  if x < 0 then raise (Bad x) else x

let[@refined.over { type_ = "x:int -> {result:int | result = x}" }] payload_caught
    (x : int) : int =
  try raise (Bad x) with Bad payload -> payload

let[@refined.over
     { type_ = "x:int -> int"; performs = [ ("Send", "payload = x") ] }] payload_perform
    (x : int) : int =
  Effect.perform (Send x)

let[@refined.over { type_ = "x:int -> {result:int | result = x + 1}" }] payload_handled
    (x : int) : int =
  Effect.Deep.match_with
    (fun () ->
      let value = Effect.perform (Send x) in
      value + 1)
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
