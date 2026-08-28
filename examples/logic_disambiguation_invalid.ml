type 'a box = Box of 'a

let[@refined.over { pre = "true"; post = "result = Box flag" }] wrong_box
    (x : int) (flag : bool) : int box =
  Box x
