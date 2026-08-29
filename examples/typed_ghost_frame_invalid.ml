let[@refined.over
     {
       pre = "true";
       post = "true";
       state = [ ("left", "value = 1") ];
       modifies = [ "left" ];
     }] violates_frame (left : int ref) (flag : bool ref) : int =
  left := 1;
  flag := false;
  !left

let[@refined.over { pre = "true"; post = "result = 0"; modifies = [ "cell" ] }] havoc
    (cell : int ref) : int =
  cell := 1;
  0

let[@refined.over { pre = "true"; post = "result = 1" }] missing_call_frame
    (cell : int ref) : int =
  let _ignored = havoc cell in
  !cell

exception Stop

let[@refined.over
     {
       pre = "true";
       raises = [ ("Stop", "true") ];
       post = "false";
       outcome_state = [ ("raise", "Stop", "left", "value = 1") ];
       outcome_modifies = [ ("raise", "Stop", "left") ];
     }] violates_outcome_frame (left : int ref) (flag : bool ref) : int =
  left := 1;
  flag := false;
  raise Stop
