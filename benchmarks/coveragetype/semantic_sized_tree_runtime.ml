let () =
  if not (Semantic_sized_tree.runtime_examples ()) then
    failwith "semantic sized-tree examples failed"
