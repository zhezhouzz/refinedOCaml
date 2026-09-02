let[@refined.over { type_ = "x:int -> {result:int | result = x}" }] escaped_alias
    (x : int) : int =
  let cell = ref x in
  let alias = cell in
  !alias
