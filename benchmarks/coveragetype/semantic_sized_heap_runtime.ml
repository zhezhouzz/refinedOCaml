let () =
  if not (Semantic_sized_heap.runtime_examples ()) then
    failwith "semantic sized-heap examples failed"
