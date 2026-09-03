(* One-constructor mutation controls for the standalone list ports.  Projecting
   the mutated head to [int] keeps the countermodel independent of datatype
   axioms: the full positive fixtures separately verify list construction. *)

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size = 1} -> floor:int -> {result:int | result >= \
          floor}";
       universals = [ "size"; "floor" ];
     }] bound_list_below_floor (size : int) (floor : int) : int =
  floor - 1

let[@refined.coverage
     {
       type_ =
         "size:{size:int | size = 1} -> item:int -> {result:int | result = \
          item}";
       universals = [ "size"; "item" ];
     }] duplicate_list_wrong_item (size : int) (item : int) : int =
  item + 1
