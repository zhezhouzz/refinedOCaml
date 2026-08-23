module Theory = struct
  let[@refined.predicate] predicate (_value : int) : bool = false

  [@@@refined.axiom
  { name = "example"; vars = [ ("x", "int") ]; body = "predicate x" }]
end

let[@refined.coverage { pre = "true"; post = "true" }] identity (value : int) :
    int =
  value

let () =
  ignore (Theory.predicate 0);
  ignore (identity 0)
