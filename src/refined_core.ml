open Refined_ir
include Refined_types

let obligations_of_cmt = Vc_backend.obligations_of_cmt

let obligations_of_cmt_with_theories =
  Vc_backend.obligations_of_cmt_with_theories

let write_rmi = Ocaml_5_3_frontend.write_rmi
let solve = Solver_backend.solve
