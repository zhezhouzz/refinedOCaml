let () =
  if not (Semantic_complete_tree.runtime_examples ()) then
    failwith "semantic complete-tree examples failed"
