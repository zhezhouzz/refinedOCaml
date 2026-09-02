let[@refined.over
     {
       type_ = "cell:int ref -> {result:int ref | result = cell}";
       result_state = "true";
       result_fresh = true;
     }] falsely_fresh (cell : int ref) : int ref =
  cell
