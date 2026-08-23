let[@refined.over { pre = "List_theory.hd l x"; post = "List_theory.mem l x" }] head_is_member
    (l : int list) (x : int) : bool =
  List_theory.mem l x
