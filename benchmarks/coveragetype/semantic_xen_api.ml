(* SPDX-License-Identifier: MIT
   Executable semantic model of the nine assertions in data/monad/xen_api.ml. *)

type select_fd_spec = Select_fd_spec of int * int
type specs = No_specs | More_specs of select_fd_spec * specs
type delay = No_delay | Delay of int
type fd = Fd of int * delay * delay * int

type xen_report =
  | Xen_report of bool * bool * bool * bool * bool * bool * bool * bool * bool

let wf_fd_size value =
  value = 0 || value = 1 || value = 100 || value = 4096 || value = 65535
  || value = 65536 || value = 65537 || value = 131072 || value = 655363

let wf_file_kind value = 0 <= value && value <= 6
let wf_timeout value = value = 0 || value = 1 || value = 100 || value = 300
let wf_total_delay value = value = 1 || value = 10 || value = 100 || value = 400
let wf_size_bound value = value = 0 || value = 2 || value = 10 || value = 100
let is_testable_kind value = 0 <= value && value <= 5
let has_immediate_timeout value = value = 0

let wf_select_fd_spec value =
  match value with
  | Select_fd_spec (kind, wait) ->
      is_testable_kind kind
      && if has_immediate_timeout kind then wait = 0 else wf_timeout wait

let rec spec_count values =
  match values with
  | No_specs -> 0
  | More_specs (_, tail) -> 1 + spec_count tail

let rec all_specs_valid values =
  match values with
  | No_specs -> true
  | More_specs (head, tail) -> wf_select_fd_spec head && all_specs_valid tail

let wf_spec_list values bound =
  wf_size_bound bound && all_specs_valid values && spec_count values <= bound

let valid_delay value total size =
  match value with
  | No_delay -> size = 0
  | Delay seconds ->
      wf_total_delay total && size >= 0 && seconds >= 0 && seconds <= total

let wf_fd value total source_size =
  match value with
  | Fd (size, delay_read, delay_write, kind) ->
      wf_total_delay total && wf_fd_size source_size && is_testable_kind kind
      && delay_read = delay_write
      &&
      if kind = 0 then size = 512 && valid_delay delay_read total 512
      else size = source_size && valid_delay delay_read total source_size

let build_report (_unit : unit) =
  let spec = Select_fd_spec (2, 100) in
  let files = More_specs (spec, More_specs (Select_fd_spec (0, 0), No_specs)) in
  let generated_fd = Fd (4096, Delay 10, Delay 10, 2) in
  Xen_report
    ( wf_fd_size 65536,
      wf_file_kind 6,
      wf_timeout 300,
      wf_total_delay 400,
      wf_size_bound 10,
      is_testable_kind 5,
      wf_select_fd_spec spec,
      wf_spec_list files 2,
      wf_fd generated_fd 100 4096 )

let[@refined.predicate] valid_xen_report (report : xen_report) : bool =
  match report with
  | Xen_report (a, b, c, d, e, f, g, h, i) ->
      a && b && c && d && e && f && g && h && i

[@@@refined.axiom
{
  name = "xen_report_intro";
  quantifiers = [];
  body =
    "valid_xen_report (Xen_report (true, true, true, true, true, true, true, \
     true, true))";
}]

[@@@refined.axiom
{
  name = "xen_report_elim";
  quantifiers = [ ("forall", "report", "xen_report") ];
  body =
    "implies (valid_xen_report report) (report = Xen_report (true, true, true, \
     true, true, true, true, true, true))";
}]

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {result:xen_report | valid_xen_report result}";
       witness_relation =
         "result = Xen_report (true, true, true, true, true, true, true, true, \
          true)";
     }] xen_api (unit_value : unit) : xen_report =
  let _unused_unit = unit_value in
  Xen_report (true, true, true, true, true, true, true, true, true)

let runtime_examples (_unit : unit) =
  let (Xen_report (a, b, c, d, e, f, g, h, i)) = build_report _unit in
  a && b && c && d && e && f && g && h && i
  && (not (wf_fd_size 65534))
  && (not (wf_file_kind 7))
  && (not (wf_timeout 200))
  && (not (wf_total_delay 0))
  && (not (wf_size_bound 3))
  && (not (is_testable_kind 6))
  && (not (wf_select_fd_spec (Select_fd_spec (0, 100))))
  && (not
        (wf_spec_list
           (More_specs
              ( Select_fd_spec (1, 100),
                More_specs
                  ( Select_fd_spec (2, 100),
                    More_specs (Select_fd_spec (3, 100), No_specs) ) ))
           2))
  && not (wf_fd (Fd (1, No_delay, Delay 0, 1)) 100 1)
