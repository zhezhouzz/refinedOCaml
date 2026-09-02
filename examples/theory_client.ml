let[@refined.over
     {
       type_ =
         "l:int list -> x:{x:int | List_theory.hd l x} -> {result:bool | \
          List_theory.mem l x}";
     }] head_is_member (l : int list) (x : int) : bool =
  List_theory.mem l x
