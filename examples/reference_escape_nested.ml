let[@refined.over { pre = "true"; post = "true" }] nested_escape (value : int) :
    int ref * int =
  (ref value, value)
