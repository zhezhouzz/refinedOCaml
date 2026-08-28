exception Bad of int

type _ Effect.t += Send : int -> int Effect.t

let[@refined.over
     { pre = "true"; post = "true"; raises = [ ("Bad", "payload = x + 1") ] }] wrong_exception_payload
    (x : int) : int =
  raise (Bad x)

let[@refined.over
     { pre = "true"; post = "true"; performs = [ ("Send", "payload = x + 1") ] }] wrong_effect_payload
    (x : int) : int =
  Effect.perform (Send x)
