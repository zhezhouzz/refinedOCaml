(* SPDX-License-Identifier: MIT
   Executable semantic model of data/monad/vellvm.ml. *)

type llvm_type =
  | Type_i of int
  | Type_void
  | Type_vector of int * llvm_type
  | Type_array of int * llvm_type
  | Type_others

type dvalue =
  | D_int of int * int
  | D_none
  | D_vector of llvm_type * dvalues
  | D_array of llvm_type * dvalues
  | D_error

and dvalues = No_values | More_values of dvalue * dvalues

type vellvm_report = Vellvm_report of bool * bool * bool * bool * bool

let rec value_count values =
  match values with
  | No_values -> 0
  | More_values (_, tail) -> 1 + value_count tail

let valid_integer width number =
  if width = 1 then 0 <= number && number <= 1
  else if width = 8 then 0 <= number && number <= 255
  else if width = 32 || width = 64 then 0 <= number && number <= 10000
  else false

let rec all_typed values expected =
  match values with
  | No_values -> true
  | More_values (head, tail) ->
      llvm_typing head expected && all_typed tail expected

and llvm_typing value expected =
  match expected with
  | Type_i width -> (
      match value with
      | D_int (actual_width, number) ->
          actual_width = width && valid_integer width number
      | _ -> false)
  | Type_void -> value = D_none
  | Type_vector (size, element_type) -> (
      match value with
      | D_vector (actual_type, values) ->
          actual_type = expected && size >= 0 && value_count values = size
          && all_typed values element_type
      | _ -> false)
  | Type_array (size, element_type) -> (
      match value with
      | D_array (actual_type, values) ->
          actual_type = expected && size >= 0 && value_count values = size
          && all_typed values element_type
      | _ -> false)
  | Type_others -> false

let build_report (_unit : unit) =
  let vector_type = Type_vector (2, Type_i 8) in
  let array_type = Type_array (1, Type_i 32) in
  Vellvm_report
    ( llvm_typing (D_int (1, 1)) (Type_i 1),
      llvm_typing (D_int (8, 255)) (Type_i 8),
      llvm_typing D_none Type_void,
      llvm_typing
        (D_vector
           (vector_type, More_values (D_int (8, 1), More_values (D_int (8, 2), No_values))))
        vector_type,
      llvm_typing
        (D_array (array_type, More_values (D_int (32, 9), No_values)))
        array_type )

let[@refined.predicate] valid_vellvm_report (report : vellvm_report) : bool =
  match report with
  | Vellvm_report (i1_ok, integer_ok, void_ok, vector_ok, array_ok) ->
      i1_ok && integer_ok && void_ok && vector_ok && array_ok

[@@@refined.axiom
{
  name = "vellvm_report_intro";
  quantifiers = [];
  body = "valid_vellvm_report (Vellvm_report (true, true, true, true, true))";
}]

[@@@refined.axiom
{
  name = "vellvm_report_elim";
  quantifiers = [ ("forall", "report", "vellvm_report") ];
  body =
    "implies (valid_vellvm_report report) (report = Vellvm_report (true, \
     true, true, true, true))";
}]

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {result:vellvm_report | valid_vellvm_report \
          result}";
       witness_relation = "result = Vellvm_report (true, true, true, true, true)";
     }] vellvm (unit_value : unit) : vellvm_report =
  let _unused_unit = unit_value in
  Vellvm_report (true, true, true, true, true)

let runtime_examples (_unit : unit) =
  let Vellvm_report (i1_ok, integer_ok, void_ok, vector_ok, array_ok) =
    build_report _unit
  in
  i1_ok && integer_ok && void_ok && vector_ok && array_ok
  && not (llvm_typing (D_int (1, 2)) (Type_i 1))
  && not (llvm_typing (D_int (16, 4)) (Type_i 16))
  && not
       (llvm_typing
          (D_vector
             ( Type_vector (2, Type_i 8),
               More_values (D_int (8, 1), No_values) ))
          (Type_vector (2, Type_i 8)))
  && not (llvm_typing D_error Type_void)
