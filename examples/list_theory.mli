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

val horn_identity : int -> int
[@@refined.horn
  {
    generics = [ ("property", "int -> bool") ];
    parameters = [ ("int", "int", "1", "property 1") ];
    result = ("int", "int", "1", "property 1");
  }]

[@@@refined.axiom
{
  name = "hd_mem";
  quantifiers = [ ("forall", "l", "'a list"); ("forall", "x", "'a") ];
  body = "implies (hd l x) (mem l x)";
}]
