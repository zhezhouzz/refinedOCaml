let[@refined.over { pre = "true"; post = "result = 1"; modifies = [ "cell" ] }] mutate
    (cell : int ref) : int =
  cell := 1;
  !cell
