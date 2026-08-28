val bad_horn : int -> int
[@@refined.horn
  {
    generics = [ ("property", "int -> bool") ];
    parameters = [ ("int", "int", "1", "property 1 || true") ];
    result = ("int", "int", "1", "property 1");
  }]
