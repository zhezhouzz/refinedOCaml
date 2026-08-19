open Refined_core

let require expected obligation =
  match (expected, solve obligation) with
  | `Valid, Valid | `Invalid, Invalid _ -> ()
  | `Valid, (Invalid _ | Unknown _) ->
      failwith (obligation.name ^ " should be valid")
  | `Invalid, (Valid | Unknown _) ->
      failwith (obligation.name ^ " should be invalid")

let () =
  obligations_of_file "../examples/valid.ml" |> List.iter (require `Valid);
  obligations_of_file "../examples/invalid.ml" |> List.iter (require `Invalid)

