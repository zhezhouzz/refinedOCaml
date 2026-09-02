let[@refined.over
     {
       type_ = "seed:int -> {result:int | result = 1}";
       state =
         [ ("left", "value = 2"); ("right", "value = 1"); ("flag", "value") ];
     }]
   [@refined.coverage
     {
       type_ = "seed:int -> {result:int | result = 1}";
       witnesses = [ ("seed", "0") ];
       state =
         [ ("left", "value = 2"); ("right", "value = 1"); ("flag", "value") ];
     }] fresh_allocations (seed : int) : int =
  let left = ref 0 in
  let right = ref 1 in
  let flag = ref true in
  left := 2;
  if !flag then !right else !right
