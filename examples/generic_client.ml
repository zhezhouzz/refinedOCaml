let[@refined.over { pre = "true"; post = "true" }] use_complement (value : int)
    : int =
  List_theory.complement
    (value
    [@refined.type
      {
        base = "Predicate";
        sort = "int -> bool";
        index = "fun item -> item > 0";
        predicate = "true";
      }])
