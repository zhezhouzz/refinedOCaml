let () =
  if not (Semantic_monad_case1.runtime_examples ()) then
    failwith "monad case1 semantic examples failed"
