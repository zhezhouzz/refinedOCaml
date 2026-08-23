module ListTheory = struct
  let[@refined.predicate] mem (_list : int list) (_element : int) : bool = false
  let[@refined.predicate] hd (_list : int list) (_element : int) : bool = false

  [@@@refined.axiom
  {
    name = "hd_mem";
    vars = [ ("l", "int list"); ("x", "int") ];
    body = "implies (hd l x) (mem l x)";
  }]
end

let[@refined.over { pre = "ListTheory.hd l x"; post = "ListTheory.mem l x" }] head_is_member
    (l : int list) (x : int) : bool =
  true
