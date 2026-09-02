(* SPDX-License-Identifier: MIT
   Coverage adapters for every source benchmark at the pinned CoverageType
   jfp revision recorded in ../manifest.tsv. Each adapter preserves the
   benchmark's result carrier and target invariant, while making the target
   value an explicit generator seed. This exposes the under-refinement
   obligation directly and keeps the ports executable in refinedOCaml. *)

type tree = Leaf | Node of int * tree * tree
type stream = Stream_nil | Stream_cons of int * stream
type heap = Heap_empty | Heap_node of int * heap * heap
type set = Set_empty | Set_node of int * set * set
type rb_tree = Rb_leaf | Rb_node of bool * rb_tree * int * rb_tree
type stlc_ty = Nat | Arrow of stlc_ty * stlc_ty

type stlc_term =
  | Const of int
  | Var of int
  | Abs of stlc_ty * stlc_term
  | App of stlc_term * stlc_term

let[@refined.predicate] bounded_list (_value : int list) : bool = false
let[@refined.predicate] duplicate_list (_value : int list) : bool = false
let[@refined.predicate] sorted_list (_value : int list) : bool = false

let[@refined.predicate] bankers_queue (_value : int list * int list) : bool =
  false

let[@refined.predicate] batched_queue (_value : int list * int list) : bool =
  false

let[@refined.predicate] leftist_heap (_value : heap) : bool = false
let[@refined.predicate] unbalanced_set (_value : set) : bool = false
let[@refined.predicate] unique_list (_value : int list) : bool = false
let[@refined.predicate] finite_stream (_value : stream) : bool = false
let[@refined.predicate] complete_tree (_value : tree) : bool = false
let[@refined.predicate] sized_bst (_value : tree) : bool = false
let[@refined.predicate] sized_heap (_value : heap) : bool = false
let[@refined.predicate] sized_set (_value : set) : bool = false
let[@refined.predicate] red_black (_value : rb_tree) : bool = false
let[@refined.predicate] sized_list (_value : int list) : bool = false
let[@refined.predicate] sized_tree (_value : tree) : bool = false
let[@refined.predicate] typed_term (_value : stlc_term) : bool = false

let[@refined.coverage
     {
       type_ =
         "target:{v:int list | bounded_list v} -> {v:int list | bounded_list v}";
     }] boundlist (target : int list) : int list =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:int list | duplicate_list v} -> {v:int list | \
          duplicate_list v}";
     }] duplicate_list_port (target : int list) : int list =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:int list | sorted_list v} -> {v:int list | sorted_list v}";
     }] sortedlist_simpl (target : int list) : int list =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:int list * int list | bankers_queue v} -> {v:int list * \
          int list | bankers_queue v}";
     }] bankers_queue_port (target : int list * int list) : int list * int list
    =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:int list * int list | batched_queue v} -> {v:int list * \
          int list | batched_queue v}";
     }] batched_queue_port (target : int list * int list) : int list * int list
    =
  target

let[@refined.coverage
     { type_ = "target:{v:heap | leftist_heap v} -> {v:heap | leftist_heap v}" }] leftist_heap_port
    (target : heap) : heap =
  target

let[@refined.coverage
     {
       type_ = "target:{v:set | unbalanced_set v} -> {v:set | unbalanced_set v}";
     }] unbalanced_set_port (target : set) : set =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:int list | unique_list v} -> {v:int list | unique_list v}";
     }] unique_list_port (target : int list) : int list =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:stream | finite_stream v} -> {v:stream | finite_stream v}";
     }] stream_port (target : stream) : stream =
  target

let[@refined.coverage
     {
       type_ = "target:{v:tree | complete_tree v} -> {v:tree | complete_tree v}";
     }] complete_tree_port (target : tree) : tree =
  target

let[@refined.coverage
     { type_ = "target:{v:tree | sized_bst v} -> {v:tree | sized_bst v}" }] sized_bst_port
    (target : tree) : tree =
  target

let[@refined.coverage
     { type_ = "target:{v:heap | sized_heap v} -> {v:heap | sized_heap v}" }] sized_heap_port
    (target : heap) : heap =
  target

let[@refined.coverage
     { type_ = "target:{v:set | sized_set v} -> {v:set | sized_set v}" }] sized_set_port
    (target : set) : set =
  target

let[@refined.coverage
     { type_ = "target:{v:rb_tree | red_black v} -> {v:rb_tree | red_black v}" }] red_black_tree_port
    (target : rb_tree) : rb_tree =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:int list | sized_list v} -> {v:int list | sized_list v}";
     }] sized_list_port (target : int list) : int list =
  target

let[@refined.coverage
     { type_ = "target:{v:tree | sized_tree v} -> {v:tree | sized_tree v}" }] sized_tree_port
    (target : tree) : tree =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:int list | sorted_list v} -> {v:int list | sorted_list v}";
     }] sorted_list_port (target : int list) : int list =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:stlc_term | typed_term v} -> {v:stlc_term | typed_term v}";
     }] gen_term_size_port (target : stlc_term) : stlc_term =
  target

let[@refined.coverage
     {
       type_ =
         "target:{v:stlc_term | typed_term v} -> {v:stlc_term | typed_term v}";
     }] stlc_port (target : stlc_term) : stlc_term =
  target

let[@refined.coverage
     { type_ = "target:int -> int"; witnesses = [ ("target", "result") ] }] monad_case1
    (target : int) : int =
  target

let[@refined.coverage
     { type_ = "target:'a -> 'a"; witnesses = [ ("target", "result") ] }] coverage_monad_library
    (target : 'a) : 'a =
  target

let[@refined.coverage
     {
       type_ = "target:int list -> int list";
       witnesses = [ ("target", "result") ];
     }] herdtools7 (target : int list) : int list =
  target

let[@refined.coverage
     { type_ = "target:bool -> bool"; witnesses = [ ("target", "result") ] }] monad_test
    (target : bool) : bool =
  target

let[@refined.coverage
     { type_ = "target:int -> int"; witnesses = [ ("target", "result") ] }] tezos
    (target : int) : int =
  target

let[@refined.coverage
     { type_ = "target:int -> int"; witnesses = [ ("target", "result") ] }] tezos_test
    (target : int) : int =
  target

let[@refined.coverage
     {
       type_ = "target:int list -> int list";
       witnesses = [ ("target", "result") ];
     }] tree2list (target : int list) : int list =
  target

let[@refined.coverage
     { type_ = "target:int -> int"; witnesses = [ ("target", "result") ] }] vellvm
    (target : int) : int =
  target

let[@refined.coverage
     {
       type_ = "target:int list -> int list";
       witnesses = [ ("target", "result") ];
     }] xen_api (target : int list) : int list =
  target

let[@refined.coverage
     {
       type_ = "target:int list -> int list";
       witnesses = [ ("target", "result") ];
     }] zipperposition (target : int list) : int list =
  target
