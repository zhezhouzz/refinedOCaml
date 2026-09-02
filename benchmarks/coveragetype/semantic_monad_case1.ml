(* SPDX-License-Identifier: MIT
   Semantic port of data/monad/case1.ml: union must cover both branches. *)

let[@refined.choose] union_choice (left : int) (_right : int) : int = left

let[@refined.coverage
     { type_ = "unit_value:unit -> {result:int | result = 1 || result = 2}" }] monad_case1
    (unit_value : unit) : int =
  let _unused_unit = unit_value in
  union_choice 1 2

let runtime_examples (_unit : unit) =
  let left = union_choice 1 2 in
  left = 1
