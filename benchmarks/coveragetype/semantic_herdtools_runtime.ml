let () =
  if not (Semantic_herdtools.runtime_examples ()) then
    failwith "herdtools semantic examples failed"
