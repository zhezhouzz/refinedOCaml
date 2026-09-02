type 'a box = Box of 'a
type 'a maybe = Nothing | Just of 'a
type 'a cell = { value : 'a }

let[@refined.over
     { type_ = "x:int -> flag:bool -> {result:int box | result = Box x}" }] mixed_box
    (x : int) (flag : bool) : int box =
  let other = Box flag in
  match other with Box _ -> Box x

let[@refined.over
     { type_ = "x:int -> flag:bool -> {result:bool box | Box flag = result}" }] reversed_box
    (x : int) (flag : bool) : bool box =
  let _other = Box x in
  Box flag

let[@refined.over
     { type_ = "x:int -> flag:bool -> {result:int maybe | result = Nothing}" }] mixed_nothing
    (x : int) (flag : bool) : int maybe =
  let other = (if flag then Nothing else Just flag : bool maybe) in
  match other with
  | Nothing -> if x = 0 then Nothing else Nothing
  | Just _ -> if x = 0 then Nothing else Nothing

let[@refined.over
     { type_ = "x:int -> flag:bool -> {result:bool maybe | Nothing = result}" }] reversed_nothing
    (x : int) (flag : bool) : bool maybe =
  let _other = (if x = 0 then Nothing else Just x : int maybe) in
  if flag then Nothing else Nothing

let[@refined.over
     {
       type_ =
         "left:int cell -> right:bool cell -> flag:{flag:bool | right.value = \
          flag} -> {result:int | result = left.value && right.value = flag}";
     }] mixed_fields (left : int cell) (right : bool cell) (flag : bool) : int =
  left.value
