type 'a box = Box of 'a

let[@refined.over { type_ = "value:'a_a box -> 'a_a box" }] open_box
    (value : 'a box) : 'a box =
  value
