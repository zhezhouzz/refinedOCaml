type _ Effect.t += Stop : int Effect.t

let[@refined.over
     { pre = "true"; post = "result = 0"; performs = [ ("Stop", "flag") ] }] unhandled
    (flag : bool) : int =
  if flag then Effect.perform Stop else 0

let[@refined.over { pre = "true"; post = "result = 1" }] handled (_unit : unit)
    : int =
  Effect.Deep.match_with
    (fun () -> Effect.perform Stop)
    ()
    {
      retc = (fun value -> value);
      exnc = raise;
      effc =
        (fun (type result) (operation : result Effect.t) ->
          match operation with
          | Stop -> Some (fun _continuation -> 1)
          | _ -> None);
    }

let[@refined.over
     { pre = "true"; post = "result = 1"; state = [ ("cell", "value = 1") ] }] handled_state
    (_unit : unit) : int =
  let cell = ref 0 in
  Effect.Deep.match_with
    (fun () ->
      cell := 1;
      Effect.perform Stop)
    ()
    {
      retc = (fun value -> value);
      exnc = raise;
      effc =
        (fun (type result) (operation : result Effect.t) ->
          match operation with
          | Stop -> Some (fun _continuation -> !cell)
          | _ -> None);
    }
