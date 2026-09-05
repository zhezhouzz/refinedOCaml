(* SPDX-License-Identifier: MIT
   Algorithm port of the pinned CoverageType source; see ../PORTS.md. *)
exception Reject

let[@refined.choose] int_gen (_unit : unit) : int = 0
let[@refined.choose] bool_gen (_unit : unit) : bool = false
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
       type_ = "unit_value:unit -> {r:int | r = 2}";
       universals = [ "unit_value" ];
       witness_relation = "true";
     }] monad_case1 (unit_value : unit) : int =
  bind
    (fun u -> bool_gen u)
    (fun x u -> if x then return 1 u else return 2 u)
    unit_value

let runtime_examples (_unit : unit) =
  monad_case1 () = 2 && bind (return 4) (fun x -> return (x + 1)) () = 5
