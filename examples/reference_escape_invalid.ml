let[@refined.over
     {
       pre = "true";
       post = "result = cell";
       result_state = "true";
       result_fresh = true;
     }] falsely_fresh (cell : int ref) : int ref =
  cell
