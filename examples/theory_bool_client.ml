let[@refined.over
     {
       type_ =
         "l:bool list -> x:{x:bool | List_theory.hd l x} -> {result:bool | \
          List_theory.mem l x}";
     }] head_is_member (l : bool list) (x : bool) : bool =
  List_theory.mem l x
