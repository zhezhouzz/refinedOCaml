let[@refined.over { type_ = "g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}" }] apply_at_zero
    (g : int -> int) : int =
  g 0

let[@refined.over { type_ = "x:int -> {r:int | r = x - 1}" }] decrement
    (x : int) : int =
  x - 1

let[@refined.over { type_ = "offset:int -> x:int -> {r:int | r = x + offset}" }] add
    (offset : int) (x : int) : int =
  x + offset

let[@refined.over
     {
       type_ =
         "f:(g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}) -> {r:int | r > \
          0}";
     }] good_anonymous (f : (int -> int) -> int) : int =
  f (fun x -> x + 1)

let[@refined.over
     {
       type_ =
         "f:(g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}) -> {r:int | r > \
          0}";
     }] bad_anonymous (f : (int -> int) -> int) : int =
  f (fun x -> x - 1)

let[@refined.over
     {
       type_ =
         "f:(g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}) -> {r:int | r > \
          0}";
     }] bad_named (f : (int -> int) -> int) : int =
  f decrement

let[@refined.over
     {
       type_ =
         "f:(g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}) -> {r:int | r > \
          0}";
     }] good_residual (f : (int -> int) -> int) : int =
  f (add 1)

let[@refined.over
     {
       type_ =
         "f:(g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}) -> {r:int | r > \
          0}";
     }] bad_residual (f : (int -> int) -> int) : int =
  f (add (-1))

let[@refined.over
     {
       type_ =
         "f:(g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}) -> g:(x:int -> \
          {r:int | r = x}) -> {r:int | r > 0}";
     }] bad_symbolic (f : (int -> int) -> int) (g : int -> int) : int =
  f g

let[@refined.over
     {
       type_ =
         "offset:int -> f:(g:(x:int -> {r:int | r > x + offset}) -> {r:int | r \
          > offset}) -> {r:int | r > offset}";
     }] good_dependent (offset : int) (f : (int -> int) -> int) : int =
  f (fun x -> x + offset + 1)

let[@refined.over
     {
       type_ =
         "offset:int -> f:(g:(x:int -> {r:int | r > x + offset}) -> {r:int | r \
          > offset}) -> {r:int | r > offset}";
     }] bad_dependent (offset : int) (f : (int -> int) -> int) : int =
  f (fun x -> x + offset)

let[@refined.over
     {
       type_ =
         "f:(g:(x:int -> {r:int | r > x}) -> {r:int | r > 0}) -> flag:bool -> \
          {r:int | r > 0}";
     }] bad_branch (f : (int -> int) -> int) (flag : bool) : int =
  f (if flag then add 1 else add (-1))

(* Before callback checking, all annotations in this call chain passed even
   though the closed program returns -1. The invalid body above must fail. *)
let counterexample (_unit : unit) : int = bad_anonymous apply_at_zero
