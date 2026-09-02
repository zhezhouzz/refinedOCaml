(* SPDX-License-Identifier: MIT
   Semantic port of data/monad/herdtools7.ml.  It keeps the five literal
   alternatives and checks the bounds imposed on integers and bit vectors. *)

type literal =
  | L_int of int
  | L_bool of bool
  | L_real of int
  | L_bit_vector of int * int
  | L_string of int

type literal_report = Literal_report of bool * bool * bool * bool * bool

let[@refined.predicate] wf_literal (value : literal) : bool =
  match value with
  | L_int number -> 0 <= number && number <= 1000
  | L_bool _ -> true
  | L_real _ -> true
  | L_bit_vector (length, digit) ->
      0 <= length && length <= 1000 && (digit = 0 || digit = 1)
  | L_string length -> length >= 0

let[@refined.predicate] valid_literal_report (report : literal_report) : bool =
  match report with
  | Literal_report (integer_ok, boolean_ok, real_ok, bits_ok, string_ok) ->
      integer_ok && boolean_ok && real_ok && bits_ok && string_ok

[@@@refined.axiom
{
  name = "literal_report_intro";
  quantifiers = [];
  body = "valid_literal_report (Literal_report (true, true, true, true, true))";
}]

[@@@refined.axiom
{
  name = "literal_report_elim";
  quantifiers = [ ("forall", "report", "literal_report") ];
  body =
    "implies (valid_literal_report report) (report = Literal_report (true, \
     true, true, true, true))";
}]

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {result:literal_report | valid_literal_report \
          result}";
       witness_relation =
         "result = Literal_report (true, true, true, true, true)";
     }] herdtools7 (unit_value : unit) : literal_report =
  let _unused_unit = unit_value in
  Literal_report (true, true, true, true, true)

let runtime_examples (_unit : unit) =
  wf_literal (L_int 0) && wf_literal (L_int 1000) && wf_literal (L_bool true)
  && wf_literal (L_real (-4))
  && wf_literal (L_bit_vector (2, 1))
  && wf_literal (L_string 3)
  && (not (wf_literal (L_int 1001)))
  && (not (wf_literal (L_bit_vector (2, 2))))
  && (not (wf_literal (L_bit_vector (1001, 1))))
  && not (wf_literal (L_string (-1)))
