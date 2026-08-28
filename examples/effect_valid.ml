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

let[@refined.over { pre = "true"; post = "result = 2" }] deep_resume
    (_unit : unit) : int =
  Effect.Deep.match_with
    (fun () ->
      let first = Effect.perform Stop in
      let second = Effect.perform Stop in
      first + second)
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

let[@refined.over
     { pre = "true"; post = "result = 2"; state = [ ("cell", "value = 2") ] }] resumed_state
    (_unit : unit) : int =
  let cell = ref 0 in
  Effect.Deep.match_with
    (fun () ->
      cell := 1;
      let resumed = Effect.perform Stop in
      cell := resumed;
      !cell)
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
                  Effect.Deep.continue continuation 2)
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
