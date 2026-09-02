let[@refined.over { type_ = "value:int -> int" }] complement_twice (value : int)
    : int =
  let complemented =
    List_theory.complement
      (value
      [@refined.type
        {
          base = "Predicate";
          sort = "int -> bool";
          index = "fun item -> item > 0";
          predicate = "true";
        }])
  in
  List_theory.complement complemented

let[@refined.over { type_ = "value:int -> int" }] horn_twice (value : int) : int
    =
  let once =
    List_theory.horn_identity
      (value
      [@refined.type
        { base = "int"; sort = "int"; index = "1"; predicate = "1 > 0" }])
  in
  List_theory.horn_identity once
