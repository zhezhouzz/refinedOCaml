let () =
  if not (Semantic_stlc.runtime_examples ()) then
    failwith "semantic STLC examples failed"
