let () =
  if not (Semantic_tezos_test.runtime_examples ()) then
    failwith "Tezos test semantic examples failed"
