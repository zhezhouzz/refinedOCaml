type 'a box = Box of 'a

let id value = value

let[@refined.over { pre = "true"; post = "result = x" }] use_int (x : int) : int
    =
  id x

let[@refined.over { pre = "true"; post = "result = x" }] use_bool (x : bool) :
    bool =
  id x
