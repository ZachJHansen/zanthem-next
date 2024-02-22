lemma:  exists N$i sqrt(N$i).
lemma: forall N1$i N2$i (N1$i >= 1 and N2$i >= 1 and N1$i < N2$i -> N1$i * N1$i < N2$i * N2$i).
lemma: forall I$i N$i (I$i*I$i <= b and sqrt(N$i) -> I$i <= N$i).
lemma: forall I$i J$i M$i ( (sqrt(M$i) and I$i > M$i and J$i > M$i ) -> (I$i*J$i > b) ).
lemma: forall I$i J$i M$i ( (I$i >= 0 and J$i >= 0 and I$i*J$i <= b ) -> (sqrt(M$i) -> (I$i <= M$i or J$i <= M$i) ) ).
lemma: forall N$i I$i J$i M$i ( (N$i <= b and I$i*J$i = N$i) -> (sqrt(M$i) -> I$i <= M$i or J$i <= M$i) ).

lemma(forward): forall X (prime(X) <- exists N1$i (exists N2$i N3$i (N2$i = a and N3$i = b and N2$i <= N1$i and N1$i <= N3$i) and not composite(N1$i) and X = N1$i)).
lemma(forward): forall X (prime(X) -> exists N1$i (exists N2$i N3$i (N2$i = a and N3$i = b and N2$i <= N1$i and N1$i <= N3$i) and not composite(N1$i) and X = N1$i)).

lemma(backward): forall X (prime(X) -> exists N$i (a <= N$i and N$i <= b and not composite(N$i) and X = N$i)).
lemma(backward): forall X (prime(X) <- exists N$i (a <= N$i and N$i <= b and not composite(N$i) and X = N$i)).