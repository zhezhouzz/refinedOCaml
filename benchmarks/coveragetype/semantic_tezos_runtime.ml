let () =
  if not (Semantic_tezos.runtime_examples ()) then
    failwith "Tezos semantic examples failed"
