let () =
  let value = Coveragetype_boundlist.bound_list_gen 4 3 in
  let empty = Coveragetype_boundlist.bound_list_gen 0 3 in
  if
    not
      (Coveragetype_boundlist.bounded value 4 3
      && Coveragetype_boundlist.bounded empty 0 3)
  then failwith "bound_list_gen violated its length/lower-bound invariant"
