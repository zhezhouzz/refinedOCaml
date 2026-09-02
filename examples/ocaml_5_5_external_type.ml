type token = external "refined_ocaml_test_token"

let[@refined.over { type_ = "value:token -> token" }] external_identity
    (value : token) =
  value
