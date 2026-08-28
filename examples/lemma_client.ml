let[@refined.over
     { pre = "Lemma_theory.q x = false"; post = "Lemma_theory.p x = false" }] use_checked_lemma
    (x : int) : int =
  if Lemma_theory.p x then x else x
