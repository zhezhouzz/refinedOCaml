let () =
  if not (Semantic_monad_library.runtime_examples ()) then
    failwith "monad library semantic examples failed"
