let[@refined.over { pre = "List_theory.mem l x"; post = "List_theory.hd l x" }] member_is_head
    (l : int list) (x : int) : bool =
  List_theory.hd l x
