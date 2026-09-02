let () =
  if not (Semantic_vellvm.runtime_examples ()) then
    failwith "Vellvm semantic examples failed"
