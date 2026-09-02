type _ Effect.t += Choose : int Effect.t

let[@refined.over { type_ = "_unit:unit -> int" }] resumes_twice (_unit : unit)
    : int =
  Effect.Deep.match_with
    (fun () -> Effect.perform Choose)
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
                  let first = Effect.Deep.continue continuation 1 in
                  first + Effect.Deep.continue continuation 2)
          | _ -> None);
    }
