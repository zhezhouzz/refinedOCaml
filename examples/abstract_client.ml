module Local = Abstract_theory.Alias

let[@refined.over { type_ = "value:t -> {result:bool | result}" }] through_alias
    (value : Abstract_theory.t) : bool =
  Local.holds value

let[@refined.over { type_ = "value:t -> {result:bool | result}" }] reflexive
    (value : Abstract_theory.t) : bool =
  Abstract_theory.equal value value
