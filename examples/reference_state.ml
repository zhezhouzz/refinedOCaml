let[@refined.over
     {
       type_ = "cell:int ref -> {result:int | result >= 1}";
       requires_state = [ ("cell", "value >= 0") ];
       state = [ ("cell", "value = old + 1 && value = result") ];
     }]
   [@refined.coverage
     {
       type_ = "cell:int ref -> {result:int | result >= 1}";
       requires_state = [ ("cell", "value >= 0") ];
       state = [ ("cell", "value = result") ];
       state_witnesses = [ ("cell", "result - 1") ];
     }] bump (cell : int ref) : int =
  cell := !cell + 1;
  !cell

let[@refined.over
     {
       type_ = "cell:int ref -> {result:int | result >= 1}";
       requires_state = [ ("cell", "value >= 0") ];
       state = [ ("cell", "value = old + 1 && value = result") ];
     }] safety_wrapper (cell : int ref) : int =
  bump cell

let[@refined.coverage
     {
       type_ = "cell:int ref -> {result:int | result >= 1}";
       requires_state = [ ("cell", "value >= 0") ];
       state = [ ("cell", "value = result") ];
       state_witnesses = [ ("cell", "result - 1") ];
     }] coverage_wrapper (cell : int ref) : int =
  bump cell
