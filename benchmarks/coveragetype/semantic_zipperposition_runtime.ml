let () =
  if not (Semantic_zipperposition.runtime_examples ()) then
    failwith "zipperposition semantic examples failed"
