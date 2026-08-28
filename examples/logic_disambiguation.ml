type 'a box = Box of 'a
type 'a maybe = Nothing | Just of 'a
type 'a cell = { value : 'a }

let[@refined.over { pre = "true"; post = "result = Box x" }] mixed_box (x : int)
    (flag : bool) : int box =
  let other = Box flag in
  match other with Box _ -> Box x

let[@refined.over { pre = "true"; post = "Box flag = result" }] reversed_box
    (x : int) (flag : bool) : bool box =
  let _other = Box x in
  Box flag

let[@refined.over { pre = "true"; post = "result = Nothing" }] mixed_nothing
    (x : int) (flag : bool) : int maybe =
  let other = (if flag then Nothing else Just flag : bool maybe) in
  match other with
  | Nothing -> if x = 0 then Nothing else Nothing
  | Just _ -> if x = 0 then Nothing else Nothing

let[@refined.over { pre = "true"; post = "Nothing = result" }] reversed_nothing
    (x : int) (flag : bool) : bool maybe =
  let _other = (if x = 0 then Nothing else Just x : int maybe) in
  if flag then Nothing else Nothing

let[@refined.over
     {
       pre = "right.value = flag";
       post = "result = left.value && right.value = flag";
     }] mixed_fields (left : int cell) (right : bool cell) (flag : bool) : int =
  left.value
