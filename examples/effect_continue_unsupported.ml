type _ Effect.t += Stop : int Effect.t

let[@refined.over { pre = "true"; post = "true" }] resumes (_unit : unit) : int
    =
  Effect.Deep.match_with
    (fun () -> Effect.perform Stop)
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
                  Effect.Deep.continue continuation 1)
          | _ -> None);
    }
