(* SPDX-License-Identifier: MIT
   Algorithm port of the pinned CoverageType source; see ../PORTS.md. *)
exception Reject

let runtime_integer = ref 0
let runtime_boolean = ref false
let[@refined.choose] int_gen (_unit : unit) : int = !runtime_integer
let[@refined.choose] bool_gen (_unit : unit) : bool = !runtime_boolean
let return (x : 'a) (_u : unit) : 'a = x
let bind (g : unit -> 'a) (f : 'a -> unit -> 'b) (_u : unit) : 'b = f (g ()) ()
let fmap (f : 'a -> 'b) (g : unit -> 'a) (_u : unit) : 'b = f (g ())

let fmap2 (f : 'a -> 'b -> 'c) (g : unit -> 'a) (h : unit -> 'b) (_u : unit) :
    'c =
  f (g ()) (h ())

let union (g : unit -> 'a) (h : unit -> 'a) (_u : unit) : 'a =
  if bool_gen () then g () else h ()

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

let rec fix (f : int -> (int -> unit -> 'a) -> unit -> 'a) (n : int) (_u : unit)
    : 'a =
  f n (fix f) ()

let[@refined.coverage
     {
       type_ = "n:{n:int | n >= 0} -> _u:unit -> {r:int | 0 <= r && r <= n}";
       universals = [ "n"; "_u" ];
       witness_relation = "true";
     }] int_bound (n : int) (_u : unit) : int =
  if n < 0 then raise Reject else int_gen () mod (n + 1)

let[@refined.coverage
     {
       type_ =
         "a:int -> b:{b:int | a <= b} -> _u:unit -> {r:int | a <= r && r <= b}";
       universals = [ "a"; "b"; "_u" ];
       witness_relation = "true";
     }] int_range (a : int) (b : int) (_u : unit) : int =
  if b < a then raise Reject else fmap (fun x -> a + x) (int_bound (b - a)) ()

let nat (_u : unit) : int =
  bind (int_bound 10)
    (fun p u ->
      if p < 5 then int_bound 10 u
      else if p < 8 then int_bound 100 u
      else if p < 9 then int_bound 1000 u
      else int_bound 10000 u)
    ()

let pair (g : unit -> 'a) (h : unit -> 'b) (_u : unit) : 'a * 'b = (g (), h ())

let option (g : unit -> 'a) (_u : unit) : 'a option =
  fmap (fun p -> if p < 2 then None else Some (g ())) (int_bound 10) ()

let oneof (l : int -> unit -> 'a) (_u : unit) : 'a =
  let n = int_gen () in
  if n < 0 then raise Reject else l n ()

let nil_gen (_i : int) (_u : unit) : 'a = raise Reject

let cons_gen (g : unit -> 'a) (l : int -> unit -> 'a) (i : int) (_u : unit) : 'a
    =
  if i = 0 then g () else l (i - 1) ()

let oneofl (l : 'a list) (_u : unit) : 'a =
  List.nth l (int_range 0 (List.length l - 1) ())

let rec frequencyl_aux (i : int) (m : int) (l : (int * 'a) list) (acc : int)
    (_u : unit) : 'a =
  match l with
  | [] -> raise Reject
  | (n, x) :: rest ->
      if bool_gen () then x else frequencyl_aux (i - 1) m rest (acc + n) ()

let frequencyl (l : (int * 'a) list) (_u : unit) : 'a =
  frequencyl_aux (List.length l)
    (List.fold_left (fun a entry -> a + fst entry) 0 l)
    l 0 ()

let frequency (weights : int list) (l : int -> unit -> 'a) (_u : unit) : 'a =
  l (int_range_inc 0 (List.length weights - 1)) ()

let numeral (_u : unit) : int = fmap (fun c -> c + 48) (int_bound 9) ()

let rec list_repeat (n : int) (g : unit -> 'a) (_u : unit) : 'a list =
  if n <= 0 then [] else g () :: list_repeat (n - 1) g ()

let[@refined.predicate] split_target (v : int * int) (n : int) : bool =
  fst v > 0 && snd v > 0 && fst v + snd v = n

let[@refined.logic] first (v : int * int) : int = fst v

[@@@refined.axiom
{
  name = "split_elim";
  quantifiers = [ ("forall", "v", "int * int"); ("forall", "n", "int") ];
  body =
    "implies (split_target v n) (v = (first v, n - first v) && first v > 0 && \
     first v < n)";
}]

let[@refined.coverage
     {
       type_ =
         "n:{n:int | n >= 2} -> _u:unit -> {r:int * int | split_target r n}";
       universals = [ "n"; "_u" ];
       witness_relation = "true";
     }] pos_split2 (n : int) (_u : unit) : int * int =
  if n < 2 then raise Reject
  else fmap (fun n1 -> (n1, n - n1)) (int_range 1 (n - 1)) ()

let[@refined.coverage
     {
       type_ = "value:int -> unit_value:unit -> {r:int | r = value}";
       universals = [ "value"; "unit_value" ];
       witness_relation = "true";
     }] return_port (value : int) (unit_value : unit) : int =
  return value unit_value

let[@refined.coverage
     {
       type_ = "value:int -> unit_value:unit -> {r:int | r = value + 1}";
       universals = [ "value"; "unit_value" ];
       witness_relation = "true";
     }] bind_port (value : int) (unit_value : unit) : int =
  bind (return value) (fun x -> return (x + 1)) unit_value

let[@refined.coverage
     {
       type_ = "value:int -> unit_value:unit -> {r:int | r = value + 2}";
       universals = [ "value"; "unit_value" ];
       witness_relation = "true";
     }] fmap_port (value : int) (unit_value : unit) : int =
  fmap (fun x -> x + 2) (return value) unit_value

let[@refined.coverage
     {
       type_ =
         "left:int -> right:int -> unit_value:unit -> {r:int | r = left + \
          right}";
       universals = [ "left"; "right"; "unit_value" ];
       witness_relation = "true";
     }] fmap2_port (left : int) (right : int) (unit_value : unit) : int =
  fmap2 (fun x y -> x + y) (return left) (return right) unit_value

let[@refined.coverage
     {
       type_ =
         "left:int -> right:int -> unit_value:unit -> {r:int | r = left || r = \
          right}";
       universals = [ "left"; "right"; "unit_value" ];
       witness_relation = "true";
     }] union_port (left : int) (right : int) (unit_value : unit) : int =
  union (return left) (return right) unit_value

let[@refined.coverage
     {
       type_ =
         "bound:{bound:int | bound >= 0} -> unit_value:unit -> {r:int | 0 <= r \
          && r <= bound}";
       universals = [ "bound"; "unit_value" ];
       witness_relation = "true";
     }] int_bound_port (bound : int) (unit_value : unit) : int =
  int_bound bound unit_value

let[@refined.coverage
     {
       type_ =
         "lower:int -> upper:{upper:int | lower <= upper} -> unit_value:unit \
          -> {r:int | lower <= r && r <= upper}";
       universals = [ "lower"; "upper"; "unit_value" ];
       witness_relation = "true";
     }] int_range_port (lower : int) (upper : int) (unit_value : unit) : int =
  int_range lower upper unit_value

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:int | 0 <= r && r <= 1000}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] nat_port (unit_value : unit) : int =
  nat unit_value

let[@refined.coverage
     {
       type_ =
         "left:int -> right:int -> unit_value:unit -> {r:int * int | r = \
          (left, right)}";
       universals = [ "left"; "right"; "unit_value" ];
       witness_relation = "true";
     }] pair_port (left : int) (right : int) (unit_value : unit) : int * int =
  pair (return left) (return right) unit_value

let[@refined.coverage
     {
       type_ =
         "value:int -> unit_value:unit -> {r:int option | r = None || r = Some \
          value}";
       universals = [ "value"; "unit_value" ];
       witness_relation = "true";
     }] option_port (value : int) (unit_value : unit) : int option =
  option (return value) unit_value

let[@refined.coverage
     {
       type_ = "value:int -> unit_value:unit -> {r:int | r = value}";
       universals = [ "value"; "unit_value" ];
       witness_relation = "true";
     }] cons_gen_port (value : int) (unit_value : unit) : int =
  cons_gen (return value) (fun i u -> i) 0 unit_value

let[@refined.coverage
     {
       type_ = "unit_value:unit -> {r:int | 48 <= r && r <= 57}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] numeral_port (unit_value : unit) : int =
  numeral unit_value

let[@refined.coverage
     {
       type_ =
         "total:{total:int | total >= 2} -> unit_value:unit -> {r:int * int | \
          split_target r total}";
       universals = [ "total"; "unit_value" ];
       witness_relation = "true";
     }] pos_split2_port (total : int) (unit_value : unit) : int * int =
  pos_split2 total unit_value

let[@refined.over
     {
       type_ =
         "f:(m:{m:int | m >= 0} -> self:(k:{k:int | 0 <= k && k < m} -> u:unit \
          -> {r:int | r = k}) -> u:unit -> {r:int | r = m}) -> n:{n:int | n >= \
          0} -> u:unit -> {r:int | r = n}";
     }]
   [@refined.measure "n"] rec fix_count
    (f : int -> (int -> unit -> int) -> unit -> int) (n : int) (u : unit) : int
    =
  f n (fix_count f) u

let default_examples (_unit : unit) =
  return 7 () = 7
  && bind (return 3) (fun x -> return (x + 2)) () = 5
  && fmap2 (fun x y -> x + y) (return 4) (return 5) () = 9
  && union (return 1) (return 2) () = 2
  && pair (return 3) (return true) () = (3, true)
  && cons_gen (return 8) nil_gen 0 () = 8
  && List.length (list_repeat 4 (return 8) ()) = 4
  && numeral () = 48
  && pos_split2 5 () = (1, 4)
  && fix
       (fun n self ->
         if n = 0 then return 0 else fmap (fun x -> x + 1) (self (n - 1)))
       4 ()
     = 4

let runtime_examples (_u : unit) =
  runtime_integer := 0;
  runtime_boolean := false;
  let defaults = default_examples () in
  let rejects =
    try
      ignore (frequencyl [ (3, 7); (1, 9) ] ());
      false
    with Reject -> true
  in
  let none = option (return 7) () = None in
  runtime_boolean := true;
  let first =
    union (return 1) (return 2) () = 1 && frequencyl [ (3, 7); (1, 9) ] () = 7
  in
  runtime_integer := 2;
  let later =
    option (return 7) () = Some 7
    && oneofl [ 4; 5; 6 ] () = 6
    && oneof (fun i -> return (i + 10)) () = 12
    && frequency [ 3; 1; 1 ] (fun i -> return (i + 10)) () = 12
    && cons_gen (return 99) (fun i -> return (i + 10)) 3 () = 12
    && list_repeat 3 (return true) () = [ true; true; true ]
  in
  let counted =
    fix_count (fun n self u -> if n = 0 then 0 else self (n - 1) u + 1) 4 () = 4
  in
  runtime_integer := 0;
  runtime_boolean := false;
  defaults && rejects && none && first && later && counted
