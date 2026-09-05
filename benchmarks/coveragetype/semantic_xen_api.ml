(* SPDX-License-Identifier: MIT
   Executable semantic model of the nine assertions in data/monad/xen_api.ml. *)

type select_fd_spec = Select_fd_spec of int * int
type specs = No_specs | More_specs of select_fd_spec * specs
type delay = No_delay | Delay of int
type fd = Fd of int * delay * delay * int

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

exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false

let[@refined.coverage
     {
       type_ =
         "lower:int -> upper:{upper:int | lower <= upper} -> {r:int | lower <= \
          r && r <= upper}";
       universals = [ "lower"; "upper" ];
       witness_relation = "true";
     }] int_range_inc (lower : int) (upper : int) : int =
  let x = int_gen () in
  if x < lower then lower else if x > upper then upper else x

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {r:int | r = 0 || r = 1 || r = 100 || r = 4096 || \
          r = 65535 || r = 65536 || r = 65537 || r = 131072 || r = 655363}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] fd_size_gen (unit_value : unit) : int =
  let i = int_range_inc 0 8 in
  if i = 0 then 0
  else if i = 1 then 1
  else if i = 2 then 100
  else if i = 3 then 4096
  else if i = 4 then 65535
  else if i = 5 then 65536
  else if i = 6 then 65537
  else if i = 7 then 131072
  else 655363

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {r:int | r = 0 || r = 1 || r = 2 || r = 3 || r = \
          4 || r = 5 || r = 6}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] file_kind_gen (unit_value : unit) : int =
  let i = int_range_inc 0 6 in
  if i = 0 then 0
  else if i = 1 then 1
  else if i = 2 then 2
  else if i = 3 then 3
  else if i = 4 then 4
  else if i = 5 then 5
  else 6

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {r:int | r = 0 || r = 1 || r = 100 || r = 300}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] timeout_gen (unit_value : unit) : int =
  let i = int_range_inc 0 3 in
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 100 else 300

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {r:int | r = 1 || r = 10 || r = 100 || r = 400}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] total_delay_gen (unit_value : unit) : int =
  let i = int_range_inc 0 3 in
  if i = 0 then 1 else if i = 1 then 10 else if i = 2 then 100 else 400

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {r:int | r = 0 || r = 2 || r = 10 || r = 100}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] size_bound_gen (unit_value : unit) : int =
  let i = int_range_inc 0 3 in
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 10 else 100

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:int | 0 <= r && r <= 5}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] testable_file_kind_gen (unit_value : unit) : int =
  let k = file_kind_gen () in
  if is_testable_kind k then k else raise Reject

let[@refined.predicate] select_target (v : select_fd_spec) : bool =
  wf_select_fd_spec v

let[@refined.logic] spec_kind (v : select_fd_spec) : int =
  match v with Select_fd_spec (k, _) -> k

let[@refined.logic] spec_wait (v : select_fd_spec) : int =
  match v with Select_fd_spec (_, w) -> w

[@@@refined.axiom
{
  name = "select_elim";
  quantifiers = [ ("forall", "v", "select_fd_spec") ];
  body =
    "implies (select_target v) (v = Select_fd_spec (spec_kind v,spec_wait v) \
     && 0 <= spec_kind v && spec_kind v <= 5 && ((spec_kind v = 0 && spec_wait \
     v = 0) || (spec_kind v > 0 && (spec_wait v = 0 || spec_wait v = 1 || \
     spec_wait v = 100 || spec_wait v = 300))))";
}]

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:select_fd_spec | select_target r}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] select_fd_spec_gen (unit_value : unit) : select_fd_spec =
  let kind = testable_file_kind_gen () in
  let wait = timeout_gen () in
  Select_fd_spec (kind, if has_immediate_timeout kind then 0 else wait)

let[@refined.predicate] sized_specs (v : specs) (n : int) : bool =
  spec_count v = n && all_specs_valid v

let[@refined.logic] specs_head (v : specs) : select_fd_spec =
  match v with No_specs -> Select_fd_spec (0, 0) | More_specs (h, _) -> h

let[@refined.logic] specs_tail (v : specs) : specs =
  match v with No_specs -> No_specs | More_specs (_, t) -> t

let[@refined.logic] specs_count (v : specs) : int = spec_count v

[@@@refined.axiom
{
  name = "specs_elim";
  quantifiers = [ ("forall", "v", "specs"); ("forall", "n", "int") ];
  body =
    "implies (sized_specs v n) ((n = 0 && v = No_specs) || (n > 0 && v = \
     More_specs (specs_head v,specs_tail v) && select_target (specs_head v) && \
     sized_specs (specs_tail v) (n - 1)))";
}]

let[@refined.coverage
     {
       type_ = "size:{size:int | size >= 0} -> {r:specs | sized_specs r size}";
       universals = [ "size" ];
       witness_relation = "true";
     }]
   [@refined.measure "size"] rec list_repeat (size : int) : specs =
  if size = 0 then No_specs
  else More_specs (select_fd_spec_gen (), list_repeat (size - 1))

let[@refined.coverage
     {
       type_ =
         "unit_value:unit -> {r:specs | 0 <= specs_count r && specs_count r <= \
          100 && sized_specs r (specs_count r)}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] file_list_gen (unit_value : unit) : specs =
  let bound = size_bound_gen () in
  let size = int_range_inc 0 bound in
  if bool_gen () then list_repeat size else list_repeat size

let[@refined.predicate] delay_target (v : delay) (total : int) (size : int) :
    bool =
  valid_delay v total size

let[@refined.logic] delay_value (v : delay) : int =
  match v with No_delay -> 0 | Delay d -> d

[@@@refined.axiom
{
  name = "delay_elim";
  quantifiers =
    [
      ("forall", "v", "delay");
      ("forall", "total", "int");
      ("forall", "size", "int");
    ];
  body =
    "implies (delay_target v total size) ((v = No_delay && size = 0) || (v = \
     Delay (delay_value v) && 0 <= delay_value v && delay_value v <= total))";
}]

let[@refined.coverage
     {
       type_ =
         "total:{total:int | total = 1 || total = 10 || total = 100 || total = \
          400} -> size:{size:int | size >= 0} -> {r:delay | delay_target r \
          total size}";
       universals = [ "total"; "size" ];
       witness_relation = "true";
     }] delay_of_size (total : int) (size : int) : delay =
  if size = 0 && bool_gen () then No_delay else Delay (int_range_inc 0 total)

let[@refined.logic] fd_size (v : fd) : int = match v with Fd (s, _, _, _) -> s

let[@refined.logic] fd_delay (v : fd) : delay =
  match v with Fd (_, d, _, _) -> d

let[@refined.logic] fd_kind (v : fd) : int = match v with Fd (_, _, _, k) -> k

let[@refined.predicate] fd_target (v : fd) : bool =
  wf_fd v 400 (if fd_kind v = 0 then 0 else fd_size v)

[@@@refined.axiom
{
  name = "fd_elim";
  quantifiers = [ ("forall", "v", "fd") ];
  body =
    "implies (fd_target v) (v = Fd (fd_size v,fd_delay v,fd_delay v,fd_kind v) \
     && 0 <= fd_kind v && fd_kind v <= 5 && ((fd_kind v = 0 && fd_size v = \
     512) || (fd_kind v > 0 && (fd_size v = 0 || fd_size v = 1 || fd_size v = \
     100 || fd_size v = 4096 || fd_size v = 65535 || fd_size v = 65536 || \
     fd_size v = 65537 || fd_size v = 131072 || fd_size v = 655363))) && \
     delay_target (fd_delay v) 400 (fd_size v))";
}]

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:fd | fd_target r}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] fd_gen (unit_value : unit) : fd =
  let total = total_delay_gen () in
  let source_size = fd_size_gen () in
  let kind = testable_file_kind_gen () in
  let size = if kind = 0 then 512 else source_size in
  let delay = delay_of_size total size in
  Fd (size, delay, delay, kind)

let runtime_examples (_u : unit) =
  select_target (select_fd_spec_gen ())
  && sized_specs (list_repeat 3) 3
  && fd_target (fd_gen ())
  && (not (select_target (Select_fd_spec (0, 100))))
  && not (fd_target (Fd (512, Delay 1, Delay 2, 0)))
