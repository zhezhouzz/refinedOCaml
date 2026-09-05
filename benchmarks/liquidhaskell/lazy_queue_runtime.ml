let () =
  if not (Liquid_lazy_queue.runtime_examples ()) then
    failwith "lazy_queue algorithm examples failed"
