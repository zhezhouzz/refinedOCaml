let[@refined.over
     {
       type_ =
         "left:int ref -> right:int ref -> {result:int | result = 1 || result \
          = 2}";
       state = [ ("left", "value = result"); ("right", "value = 2") ];
     }]
   [@refined.coverage
     {
       type_ = "left:int ref -> right:int ref -> {result:int | result = 2}";
       state = [ ("left", "value = 2"); ("right", "value = 2") ];
       state_witnesses = [ ("left", "0"); ("right", "0") ];
     }] touch_two (left : int ref) (right : int ref) : int =
  left := 1;
  right := 2;
  !left

let[@refined.over
     {
       type_ = "cell:int ref -> {result:int | result = 2}";
       state = [ ("cell", "value = 2") ];
     }] aliased (cell : int ref) : int =
  touch_two cell cell

let[@refined.coverage
     {
       type_ = "cell:int ref -> {result:int | result = 2}";
       state = [ ("cell", "value = 2") ];
       state_witnesses = [ ("cell", "0") ];
     }] aliased_coverage (cell : int ref) : int =
  touch_two cell cell
