let[@refined.over
     { type_ = "x:int -> int"; state = [ ("missing", "value = 0") ] }] unknown_cell
    (x : int) : int =
  let cell = ref x in
  !cell
