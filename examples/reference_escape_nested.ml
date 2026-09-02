let[@refined.over { type_ = "value:int -> int ref * int" }] nested_escape
    (value : int) : int ref * int =
  (ref value, value)
