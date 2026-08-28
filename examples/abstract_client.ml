module Local = Abstract_theory.Alias

let[@refined.over { pre = "true"; post = "result" }] through_alias
    (value : Abstract_theory.t) : bool =
  Local.holds value

let[@refined.over { pre = "true"; post = "result" }] reflexive
    (value : Abstract_theory.t) : bool =
  Abstract_theory.equal value value
