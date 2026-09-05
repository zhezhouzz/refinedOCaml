(* SPDX-License-Identifier: MIT
   Reproduction of the pinned upstream eager self binding, with names encoded
   by integers. This file deliberately retains the construction-time recursion. *)
type term =
  | Var of int
  | App_two of int * term * term
  | App_one of int * term
  | Ite of term * term * term

let rec default_fuel n =
  let base () = Var 0 in
  let self = default_fuel (n - 1) in
  if n <= 0 then base
  else fun () ->
    match n mod 6 with
    | 0 -> base ()
    | 1 -> App_two (0, self (), self ())
    | 2 -> App_two (1, self (), self ())
    | 3 -> App_one (2, self ())
    | 4 -> App_one (3, self ())
    | _ -> Ite (self (), self (), self ())

let () =
  let overflows =
    try
      ignore (default_fuel 0 ());
      false
    with Stack_overflow -> true
  in
  if not overflows then failwith "upstream eager recursion no longer reproduces"
