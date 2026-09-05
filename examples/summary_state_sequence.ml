(* A continuation can use the state guaranteed by an earlier call, but a
   call cannot use its own postcondition or a future call's postcondition. *)
let[@refined.over
     { type_ = "cell:int ref -> unit"; state = [ ("cell", "value = 1") ] }] put_one
    (cell : int ref) : unit =
  cell := 1

let[@refined.over
     {
       type_ = "cell:int ref -> {r:int | r > 0}";
       requires_state = [ ("cell", "value > 0") ];
     }] positive (cell : int ref) : int =
  !cell

let[@refined.over
     {
       type_ = "cell:int ref -> unit";
       requires_state = [ ("cell", "value > 0") ];
       state = [ ("cell", "value = 1") ];
     }] guarded_put (cell : int ref) : unit =
  cell := 1

let[@refined.over
     { type_ = "cell:int ref -> {r:int | r > 0}"; modifies = [ "cell" ] }] earlier_state
    (cell : int ref) : int =
  put_one cell;
  positive cell

let[@refined.over
     { type_ = "cell:int ref -> {r:int | r > 0}"; modifies = [ "cell" ] }] self_state
    (cell : int ref) : int =
  guarded_put cell;
  positive cell

let[@refined.over { type_ = "cell:int ref -> unit"; modifies = [ "cell" ] }] future_state
    (cell : int ref) : unit =
  let _x = positive cell in
  put_one cell

let[@refined.over
     {
       type_ = "flag:bool -> cell:int ref -> {r:int | r > 0}";
       modifies = [ "cell" ];
     }] branch_state (flag : bool) (cell : int ref) : int =
  if flag then (
    put_one cell;
    positive cell)
  else 1

let[@refined.over
     {
       type_ = "flag:bool -> cell:int ref -> {r:int | r > 0}";
       modifies = [ "cell" ];
     }] bad_branch_state (flag : bool) (cell : int ref) : int =
  if flag then put_one cell else ();
  positive cell
