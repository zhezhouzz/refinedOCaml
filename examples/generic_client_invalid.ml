let[@refined.over { type_ = "value:int -> int" }] invalid_generic_call
    (value : int) : int =
  List_theory.require_zero
    (value
    [@refined.type
      {
        base = "Predicate";
        sort = "int -> bool";
        index = "fun item -> item > 0";
        predicate = "true";
      }])
