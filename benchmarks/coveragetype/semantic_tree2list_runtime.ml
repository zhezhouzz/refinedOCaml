let () =
  if not (Semantic_tree2list.runtime_examples ()) then
    failwith "tree-to-list semantic examples failed"
