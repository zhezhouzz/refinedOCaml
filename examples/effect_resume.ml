type _ Effect.t += Stop : int Effect.t

let[@refined.over { type_ = "_unit:unit -> {result:int | result = 42}" }] resumes
    (_unit : unit) : int =
  Effect.Deep.match_with
    (fun () ->
      let value = Effect.perform Stop in
      value + 1)
    ()
    {
      retc = (fun value -> value);
      exnc = raise;
      effc =
        (fun (type result) (operation : result Effect.t) ->
          match operation with
          | Stop ->
              Some
                (fun (continuation : (result, int) Effect.Deep.continuation) ->
                  Effect.Deep.continue continuation 41)
          | _ -> None);
    }
