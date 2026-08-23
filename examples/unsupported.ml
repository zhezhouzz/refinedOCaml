let[@refined.over { pre = "true"; post = "result = 1" }] mutate (cell : int ref)
    : int =
  cell := 1;
  !cell
