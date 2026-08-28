type 'a box = Box of 'a

let[@refined.over { pre = "true"; post = "true" }] open_box (value : 'a box) :
    'a box =
  value
