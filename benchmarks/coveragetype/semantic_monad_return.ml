(* SPDX-License-Identifier: MIT
   Semantic port of data/monad/test.ml: return preserves its value. *)

let[@refined.coverage
     { type_ = "value:int -> int"; witness_relation = "value = result" }] monad_test
    (value : int) : int =
  value

let runtime_examples (_unit : unit) = monad_test 37 = 37
