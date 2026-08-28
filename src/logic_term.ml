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

module Strings = Set.Make (String)

let theory_symbols term =
  let rec collect symbols term =
    match term.desc with
    | Variable _ | Integer _ | Boolean _ -> symbols
    | Application (head, arguments) ->
        let symbols =
          match head with
          | Logic symbol -> Strings.add symbol.Typed_core.logic_name.key symbols
          | Constructor constructor | Selector (constructor, _) ->
              Strings.add constructor.Typed_core.symbol.key symbols
          | Builtin _ -> symbols
        in
        List.fold_left collect symbols arguments
  in
  collect Strings.empty term |> Strings.elements
