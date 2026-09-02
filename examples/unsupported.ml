let[@refined.over
     {
       type_ = "cell:int ref -> {result:int | result = 1}";
       modifies = [ "cell" ];
     }] mutate (cell : int ref) : int =
  cell := 1;
  !cell
