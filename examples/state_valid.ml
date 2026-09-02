exception Stop

let[@refined.over
     {
       type_ = "x:int -> {result:int | result = x + 1}";
       state = [ ("cell", "old = x && value = old + 1 && value = result") ];
     }] bump (x : int) : int =
  let cell = ref x in
  cell := !cell + 1;
  !cell

let[@refined.over
     {
       type_ = "flag:bool -> {result:int | result = 1 || result = 2}";
       state = [ ("cell", "value = result") ];
     }] branch_write (flag : bool) : int =
  let cell = ref 0 in
  if flag then cell := 1 else cell := 2;
  !cell

let[@refined.over
     {
       type_ = "_unit:unit -> {result:int | result = 1}";
       state = [ ("cell", "value = 1") ];
     }] handled_state (_unit : unit) : int =
  let cell = ref 0 in
  try
    cell := 1;
    raise Stop
  with Stop -> !cell
