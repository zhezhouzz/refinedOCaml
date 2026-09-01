type token = external "refined_ocaml_test_token"

let[@refined.over { pre = "true"; post = "true" }] external_identity
    (value : token) =
  value
