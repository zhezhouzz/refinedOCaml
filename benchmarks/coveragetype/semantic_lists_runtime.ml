let () =
  if not (Semantic_lists.runtime_examples ()) then
    failwith "semantic list examples failed"
