let[@refined.over
     {
       pre = "true";
       post = "true";
       state = [ ("left", "true"); ("right", "true") ];
     }] touch_two (left : int ref) (right : int ref) : int =
  left := 1;
  right := 2;
  !left

let[@refined.over { pre = "true"; post = "true" }] aliased (cell : int ref) :
    int =
  touch_two cell cell
