type _ Effect.t += Stop : int Effect.t

let[@refined.over
     { pre = "true"; post = "true"; performs = [ ("Stop", "not flag") ] }] wrong_performed_post
    (flag : bool) : int =
  if flag then Effect.perform Stop else 0

let[@refined.over { pre = "true"; post = "true" }] unlisted (flag : bool) : int
    =
  if flag then Effect.perform Stop else 0
