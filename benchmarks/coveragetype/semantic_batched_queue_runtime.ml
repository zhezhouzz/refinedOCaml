let () =
  if not (Semantic_batched_queue.runtime_examples ()) then
    failwith "semantic batched queue examples failed"
