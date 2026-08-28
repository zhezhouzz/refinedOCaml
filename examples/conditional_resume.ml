type _ Effect.t += Choose : int Effect.t
type _ Effect.t += Send : int -> int Effect.t

let[@refined.over
     {
       pre = "true";
       post = "(flag && result = 42) || (not flag && result = 7)";
     }] conditional (flag : bool) : int =
  Effect.Deep.match_with
    (fun () ->
      let value = Effect.perform Choose in
      value + 1)
    ()
    {
      retc = (fun value -> value);
      exnc = raise;
      effc =
        (fun (type result) (operation : result Effect.t) ->
          match operation with
          | Choose ->
              Some
                (fun (continuation : (result, int) Effect.Deep.continuation) ->
                  if flag then Effect.Deep.continue continuation 41 else 7)
          | _ -> None);
    }

let[@refined.over { pre = "true"; post = "result >= 0" }] payload_conditional
    (input : int) : int =
  Effect.Deep.match_with
    (fun () -> Effect.perform (Send input))
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
                  if payload >= 0 then Effect.Deep.continue continuation payload
                  else 0)
          | _ -> None);
    }
