(* SPDX-License-Identifier: MIT
   Algorithm port of the pinned CoverageType source; see ../PORTS.md. *)
let[@refined.coverage
     {
       type_ = "value:'a -> unit_value:unit -> {r:'a | r = value}";
       universals = [ "value"; "unit_value" ];
     }] monad_test (value : 'a) (unit_value : unit) : 'a =
  let _u = unit_value in
  value

let runtime_examples (_unit : unit) =
  monad_test 37 () = 37 && monad_test true ()
