type 'a token = Empty | Token of 'a

let[@refined.coverage
     {
       type_ = "x:int -> {result:int | result >= 0}";
       ghosts = [ ("ticket", "int token") ];
       witness_relation =
         "(ticket = Empty && x = result) || (ticket = Token(result) && x = \
          result)";
     }] adt_ghost (x : int) : int =
  x

let[@refined.coverage
     {
       type_ = "x:int -> {result:int | result >= 0}";
       witness_relation = "x = result";
     }] adt_ghost_wrapper (x : int) : int =
  adt_ghost x

let[@refined.over
     {
       type_ = "left:int ref -> flag:bool ref -> {result:int | result = 1}";
       requires_state = [ ("flag", "value") ];
       state = [ ("left", "value = 1") ];
       modifies = [ "left" ];
     }]
   [@refined.coverage
     {
       type_ = "left:int ref -> flag:bool ref -> {result:int | result = 1}";
       state = [ ("left", "value = 1") ];
       modifies = [ "left" ];
       witness_relation = "old_left = 0 && old_flag";
     }] framed_write (left : int ref) (flag : bool ref) : int =
  left := 1;
  if !flag then !left else !left

let[@refined.over
     {
       type_ = "left:int ref -> flag:bool ref -> {result:bool | result}";
       requires_state = [ ("flag", "value") ];
       modifies = [ "left" ];
     }]
   [@refined.coverage
     {
       type_ = "left:int ref -> flag:bool ref -> {result:bool | result}";
       state = [ ("left", "value = 1") ];
       modifies = [ "left" ];
       witness_relation = "old_left = 0 && old_flag";
     }] framed_wrapper (left : int ref) (flag : bool ref) : bool =
  let _written = framed_write left flag in
  !flag

exception Stop

let[@refined.over
     {
       type_ = "left:int ref -> flag:bool ref -> {result:int | false}";
       raises = [ ("Stop", "true") ];
       outcome_state = [ ("raise", "Stop", "left", "value = 1") ];
       outcome_modifies = [ ("raise", "Stop", "left") ];
     }]
   [@refined.coverage
     {
       type_ = "left:int ref -> flag:bool ref -> {result:int | false}";
       outcomes = [ ("raise", "Stop", "true", [], "old_left = 0 && old_flag") ];
       outcome_state = [ ("raise", "Stop", "left", "value = 1") ];
       outcome_modifies = [ ("raise", "Stop", "left") ];
     }] framed_raise (left : int ref) (flag : bool ref) : int =
  left := 1;
  raise Stop

let[@refined.over
     {
       type_ = "left:int ref -> flag:bool ref -> {result:bool | result}";
       requires_state = [ ("flag", "value") ];
       modifies = [ "left" ];
     }]
   [@refined.coverage
     {
       type_ = "left:int ref -> flag:bool ref -> {result:bool | result}";
       state = [ ("left", "value = 1") ];
       modifies = [ "left" ];
       witness_relation = "old_left = 0 && old_flag";
     }] framed_raise_wrapper (left : int ref) (flag : bool ref) : bool =
  try
    let _unreachable = framed_raise left flag in
    true
  with Stop -> !flag
