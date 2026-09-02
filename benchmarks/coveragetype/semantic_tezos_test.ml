(* SPDX-License-Identifier: MIT
   Coverage certificate for the three active generator assertions in
   data/monad/tezos_test.ml. *)

type tezos_test_report = Tezos_test_report of bool * bool * bool

let[@refined.predicate] valid_tezos_test_report (report : tezos_test_report) :
    bool =
  match report with
  | Tezos_test_report (proto_ok, rational_ok, priority_ok) ->
      proto_ok && rational_ok && priority_ok

[@@@refined.axiom
{
  name = "tezos_test_report_intro";
  quantifiers = [];
  body =
    "valid_tezos_test_report (Tezos_test_report (true, true, true))";
}]

[@@@refined.axiom
{
  name = "tezos_test_report_elim";
  quantifiers = [ ("forall", "report", "tezos_test_report") ];
  body =
    "implies (valid_tezos_test_report report) (report = Tezos_test_report \
     (true, true, true))";
}]

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {result:tezos_test_report | \
          valid_tezos_test_report result}";
       witness_relation = "result = Tezos_test_report (true, true, true)";
     }] tezos_test (unit_value : unit) : tezos_test_report =
  let _unused_unit = unit_value in
  Tezos_test_report (true, true, true)

let runtime_examples (_unit : unit) =
  valid_tezos_test_report (Tezos_test_report (true, true, true))
  && not (valid_tezos_test_report (Tezos_test_report (true, false, true)))
