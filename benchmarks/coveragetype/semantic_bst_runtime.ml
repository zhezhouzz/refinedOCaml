let () =
  if not (Semantic_bst.runtime_examples ()) then
    failwith "semantic BST examples failed"
