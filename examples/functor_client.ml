module First = Functor_theory.Make (Functor_theory.Arg1)
module First_again = Functor_theory.Make (Functor_theory.Arg1)
module Second = Functor_theory.Make (Functor_theory.Arg2)
module Fresh1 = Functor_theory.Fresh ()
module Fresh2 = Functor_theory.Fresh ()

let[@refined.over { type_ = "value:First.t -> {result:bool | result}" }] first_mark
    (value : First.t) : bool =
  First.mark value

let[@refined.over { type_ = "value:First_again.t -> {result:bool | result}" }] first_again_mark
    (value : First_again.t) : bool =
  First_again.mark value

let[@refined.over { type_ = "value:Second.t -> {result:bool | result}" }] second_mark
    (value : Second.t) : bool =
  Second.mark value

let[@refined.over { type_ = "value:Fresh1.t -> {result:bool | result}" }] fresh1_mark
    (value : Fresh1.t) : bool =
  Fresh1.mark value

let[@refined.over { type_ = "value:Fresh2.t -> {result:bool | result}" }] fresh2_mark
    (value : Fresh2.t) : bool =
  Fresh2.mark value
