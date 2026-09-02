let[@refined.over
     {
       type_ =
         "l:int list -> x:{x:int | List_theory.mem l x} -> {result:bool | \
          List_theory.hd l x}";
     }] member_is_head (l : int list) (x : int) : bool =
  List_theory.hd l x
