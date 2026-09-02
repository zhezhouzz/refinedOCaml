let () =
  if not (Semantic_stream.runtime_examples ()) then
    failwith "semantic stream examples failed"
