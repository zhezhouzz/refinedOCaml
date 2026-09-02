let[@refined.over
     {
       type_ =
         "x:{x:int | Lemma_theory.q x = false} -> {result:int | Lemma_theory.p \
          x = false}";
     }] use_checked_lemma (x : int) : int =
  if Lemma_theory.p x then x else x
