external choose : int -> int -> int = "refined_choose" [@@refined.choose]

let[@refined.over
     { pre = "true"; post = "true"; state = [ ("cell", "value = 3") ] }] wrong_nondeterministic_state
    (seed : int) : int =
  let cell = ref seed in
  choose
    (cell := 1;
     !cell)
    (cell := 2;
     !cell)
