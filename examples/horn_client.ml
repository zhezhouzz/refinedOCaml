let[@refined.over { pre = "true"; post = "true" }] use_horn (value : int) : int
    =
  List_theory.horn_identity
    (value
    [@refined.type
      { base = "int"; sort = "int"; index = "1"; predicate = "1 > 0" }])
