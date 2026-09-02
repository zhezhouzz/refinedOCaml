module Theory = struct
  let[@refined.predicate] predicate (_value : int) : bool = false

  [@@@refined.axiom
  {
    name = "example";
    quantifiers = [ ("forall", "x", "int") ];
    body = "predicate x";
  }]
end

let[@refined.coverage { type_ = "value:int -> int" }] identity (value : int) :
    int =
  value

let () =
  ignore (Theory.predicate 0);
  ignore (identity 0)
