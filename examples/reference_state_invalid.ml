let[@refined.coverage
     {
       type_ = "cell:int ref -> {result:int | result >= 1}";
       state = [ ("cell", "value = result") ];
       state_witnesses = [ ("cell", "result") ];
     }] wrong_initial_state (cell : int ref) : int =
  cell := !cell + 1;
  !cell
