let () =
  if not (Coveragetype_leftist_heap.runtime_examples ()) then
    failwith "leftist heap executable predicate rejected its semantic examples"
