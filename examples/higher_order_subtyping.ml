let[@refined.over { type_ = "z:int -> {result:int | result = z + 2}" }] add_two
    (z : int) : int =
  z + 2

let[@refined.over
     {
       type_ =
         "f:(y:{y:int | y >= 0} -> {r:int | r > y}) -> x:{x:int | x >= 0} -> \
          {result:int | result > x}";
     }] apply_positive (f : int -> int) (x : int) : int =
  f x

(* [add_two] accepts a strictly larger domain than [apply_positive] requires
   and guarantees a stronger result.  This needs semantic arrow subtyping;
   alpha-equivalent contract equality is insufficient. *)
let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] use_add_two
    (x : int) : int =
  apply_positive add_two x

let[@refined.over
     { type_ = "z:{z:int | z > 0} -> {result:int | result = z + 1}" }] positive_only
    (z : int) : int =
  z + 1

(* The callback cannot accept zero, so contravariant domain checking must make
   this caller invalid even though the callback's result is strong enough. *)
let[@refined.over { type_ = "x:{x:int | x >= 0} -> {result:int | result > x}" }] use_positive_only
    (x : int) : int =
  apply_positive positive_only x
