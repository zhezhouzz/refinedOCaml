let[@refined.over
     { pre = "true"; post = "true"; state = [ ("cell", "value = 0") ] }] wrong_state
    (x : int) : int =
  let cell = ref x in
  cell := 1;
  !cell
