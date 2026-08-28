type head =
  | Builtin of string
  | Logic of Typed_core.logic_symbol
  | Constructor of Typed_core.constructor
  | Selector of Typed_core.constructor * int

type t = { desc : desc; sort : Typed_core.sort }

and desc =
  | Variable of string
  | Integer of int
  | Boolean of bool
  | Application of head * t list

val theory_symbols : t -> string list
