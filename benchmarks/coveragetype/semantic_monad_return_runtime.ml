let () =
  if not (Semantic_monad_return.runtime_examples ()) then
    failwith "monad return semantic examples failed"
