external choose : int -> int -> int = "refined_choose" [@@refined.choose]

let[@refined.over
     { type_ = "_unit:unit -> {result:int | result = 0 || result = 1}" }]
   [@refined.coverage
     { type_ = "_unit:unit -> {result:int | result = 0 || result = 1}" }] bit
    (_unit : unit) : int =
  choose 0 1
