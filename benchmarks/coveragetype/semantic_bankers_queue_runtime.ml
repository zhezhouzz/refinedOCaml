let () =
  if not (Semantic_bankers_queue.runtime_examples ()) then
    failwith "semantic bankers queue examples failed"
