lemma: forall X N1$i N2$i ( (N1$i > 1 and N2$i > 1 and X = N1$i * N2$i) -> (N1$i <= X and N2$i <= X) ).
lemma: forall X (prime(X) <-  exists N1$i (exists N2$i (N2$i = n and 2 <= N1$i and N1$i <= N2$i) and not composite_1(N1$i) and X = N1$i)).
lemma: forall X (prime(X)  -> exists N1$i (exists N2$i (N2$i = n and 2 <= N1$i and N1$i <= N2$i) and not composite_1(N1$i) and X = N1$i)).