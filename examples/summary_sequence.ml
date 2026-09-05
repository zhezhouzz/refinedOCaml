let[@refined.over { type_ = "x:int -> {r:int | r > x}" }] increment (x : int) :
    int =
  x + 1

let[@refined.over { type_ = "x:{x:int | x > 0} -> {r:int | r > 0}" }] positive
    (x : int) : int =
  x

let[@refined.over { type_ = "_unit:unit -> {r:int | r > 0}" }] earlier_result
    (_unit : unit) : int =
  positive (increment 0)

let[@refined.over
     {
       type_ =
         "f:(x:int -> {r:int | r > x}) -> g:(x:{x:int | x > 0} -> {r:int | r > \
          0}) -> {r:int | r > 0}";
     }] earlier_symbolic (f : int -> int) (g : int -> int) : int =
  g (f 0)

(* The impossible summary below must not discharge an earlier domain check,
   including its own. Both the callee body and the invalid caller must fail. *)
let[@refined.over { type_ = "x:{x:int | x > 0} -> {r:int | false}" }] impossible
    (x : int) : int =
  x

let[@refined.over { type_ = "_unit:unit -> int" }] self_justification
    (_unit : unit) : int =
  impossible 0

let[@refined.over { type_ = "_unit:unit -> int" }] future_justification
    (_unit : unit) : int =
  let ignored = positive 0 in
  impossible (ignored + 1)

let[@refined.over { type_ = "f:(x:{x:int | x > 0} -> {r:int | false}) -> int" }] symbolic_self_justification
    (f : int -> int) : int =
  f 0
