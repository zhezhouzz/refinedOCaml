let[@refined.over
     {
       type_ = "x:{v:int | v >= 0} -> y:{v:int | v >= x} -> {v:int | v = x + y}";
     }] add_nonnegative (x : int) (y : int) : int =
  x + y

let[@refined.over { type_ = "unit:unit -> unit" }] bad_partial_stage
    (unit : unit) : unit =
  let _invalid_closure = add_nonnegative (-1) in
  unit
