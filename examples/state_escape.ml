let[@refined.over { pre = "true"; post = "true" }] escaped_alias (x : int) : int
    =
  let cell = ref x in
  let alias = cell in
  !alias
