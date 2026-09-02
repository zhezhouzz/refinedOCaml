let () =
  if not (Semantic_xen_api.runtime_examples ()) then
    failwith "Xen API semantic examples failed"
