type 'a maybe = Nothing | Just of 'a

let[@refined.over { pre = "true"; post = "Nothing = Nothing" }] ambiguous_nothing
    (x : int) (flag : bool) : int =
  let _left = (Just x : int maybe) in
  let _right = (Just flag : bool maybe) in
  x
