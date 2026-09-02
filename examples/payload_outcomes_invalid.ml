exception Bad of int

type _ Effect.t += Send : int -> int Effect.t

let[@refined.over
     { type_ = "x:int -> int"; raises = [ ("Bad", "payload = x + 1") ] }] wrong_exception_payload
    (x : int) : int =
  raise (Bad x)

let[@refined.over
     { type_ = "x:int -> int"; performs = [ ("Send", "payload = x + 1") ] }] wrong_effect_payload
    (x : int) : int =
  Effect.perform (Send x)
