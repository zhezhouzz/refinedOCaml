module ListTheory = struct
  let[@refined.predicate] mem (_list : int list) (_element : int) : bool = false
  let[@refined.predicate] hd (_list : int list) (_element : int) : bool = false
  let[@refined.predicate] witnessed (_value : int) : bool = false

  [@@@refined.axiom
  {
    name = "hd_mem";
    quantifiers = [ ("forall", "l", "int list"); ("forall", "x", "int") ];
    body = "implies (hd l x) (mem l x)";
  }]

  [@@@refined.axiom
  {
    name = "has_witness";
    quantifiers =
      [ ("forall", "x", "int"); ("exists", "y", "int"); ("forall", "z", "int") ];
    body = "y = x && witnessed x && z = z";
  }]
end

let[@refined.over
     {
       type_ =
         "l:int list -> x:{v:int | ListTheory.hd l v} -> {v:bool | \
          ListTheory.mem l x}";
     }] head_is_member (l : int list) (x : int) : bool =
  true

let[@refined.over { type_ = "x:int -> {v:bool | ListTheory.witnessed x}" }] witness_exists
    (x : int) : bool =
  true
