type _ Effect.t += Stop : int Effect.t

let[@refined.over
     { type_ = "flag:bool -> int"; performs = [ ("Stop", "not flag") ] }] wrong_performed_post
    (flag : bool) : int =
  if flag then Effect.perform Stop else 0

let[@refined.over { type_ = "flag:bool -> int" }] unlisted (flag : bool) : int =
  if flag then Effect.perform Stop else 0
