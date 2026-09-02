exception Bad

let[@refined.over
     {
       type_ = "_unit:unit -> {result:int | false}";
       raises = [ ("Bad", "true") ];
       outcome_state = [ ("raise", "Bad", "cell", "value = 2") ];
     }] wrong_abnormal_state (_unit : unit) : int =
  let cell = ref 0 in
  cell := 1;
  raise Bad
