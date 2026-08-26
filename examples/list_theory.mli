val mem : 'a list -> 'a -> bool [@@refined.predicate]
val hd : 'a list -> 'a -> bool [@@refined.predicate]

val complement : int -> int
[@@refined.hindley
  {
    generics = [ ("property", "int -> bool") ];
    parameters = [ ("Predicate", "int -> bool", "property", "true") ];
    result =
      ("Predicate", "int -> bool", "fun value -> not (property value)", "true");
  }]

val require_zero : int -> int
[@@refined.hindley
  {
    generics = [ ("property", "int -> bool") ];
    parameters = [ ("Predicate", "int -> bool", "property", "property 0") ];
    result = ("Predicate", "int -> bool", "property", "true");
  }]

[@@@refined.axiom
{
  name = "hd_mem";
  vars = [ ("l", "'a list"); ("x", "'a") ];
  body = "implies (hd l x) (mem l x)";
}]
