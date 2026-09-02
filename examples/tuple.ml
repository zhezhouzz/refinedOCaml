let[@refined.over { type_ = "left:int -> right:int -> int * int" }]
   [@refined.coverage { type_ = "left:int -> right:int -> int * int" }] pair
    (left : int) (right : int) : int * int =
  (left, right)
