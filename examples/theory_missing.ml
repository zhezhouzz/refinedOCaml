module ListTheory = struct
  let[@refined.predicate] mem (_list : int list) (_element : int) : bool = false
  let[@refined.predicate] hd (_list : int list) (_element : int) : bool = false
end

let[@refined.over { pre = "ListTheory.hd l x"; post = "ListTheory.mem l x" }] unproved_head_is_member
    (l : int list) (x : int) : bool =
  true
