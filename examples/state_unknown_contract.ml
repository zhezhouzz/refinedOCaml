let[@refined.over
     { pre = "true"; post = "true"; state = [ ("missing", "value = 0") ] }] unknown_cell
    (x : int) : int =
  let cell = ref x in
  !cell
