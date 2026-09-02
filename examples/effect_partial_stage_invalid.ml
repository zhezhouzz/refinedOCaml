let[@refined.over
     {
       type_ =
         "cell:int ref -> x:{x:int | x >= 0} -> y:int -> {result:int | result \
          = x + y}";
       state = [ ("cell", "value = old + 1") ];
     }] constrained_bump_add (cell : int ref) (x : int) (y : int) : int =
  cell := !cell + 1;
  x + y

let[@refined.over
     { type_ = "cell:int ref -> unit"; state = [ ("cell", "value = old") ] }] bad_effect_partial_stage
    (cell : int ref) : unit =
  let _pending = constrained_bump_add cell (-1) in
  cell := !cell
