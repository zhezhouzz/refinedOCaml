type 'a maybe = Nothing | Just of 'a

let[@refined.over
     { type_ = "x:int -> flag:bool -> {result:int | Nothing = Nothing}" }] ambiguous_nothing
    (x : int) (flag : bool) : int =
  let _left = (Just x : int maybe) in
  let _right = (Just flag : bool maybe) in
  x
