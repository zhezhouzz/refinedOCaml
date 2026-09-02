let[@refined.over
     {
       type_ = "cell:int ref -> x:int -> y:int -> {result:int | result = x + y}";
       requires_state = [ ("cell", "value >= 0") ];
       state = [ ("cell", "value = old + 1") ];
     }] bump_add (cell : int ref) (x : int) (y : int) : int =
  cell := !cell + 1;
  x + y

let[@refined.over
     {
       type_ = "cell:int ref -> y:int -> {result:int | result = 3 + y}";
       requires_state = [ ("cell", "value >= 0") ];
       state = [ ("cell", "value = old + 1") ];
     }] use_effect_partial (cell : int ref) (y : int) : int =
  let pending = bump_add cell 3 in
  pending y
