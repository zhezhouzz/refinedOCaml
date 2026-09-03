let () =
  let value = Coveragetype_duplicate_list.duplicate_list_gen 4 7 in
  let empty = Coveragetype_duplicate_list.duplicate_list_gen 0 7 in
  if
    not
      (Coveragetype_duplicate_list.duplicates value 4 7
      && Coveragetype_duplicate_list.duplicates empty 0 7)
  then failwith "duplicate_list_gen violated its length/equality invariant"
