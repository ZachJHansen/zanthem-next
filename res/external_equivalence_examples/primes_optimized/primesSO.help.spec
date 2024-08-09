lemma: exists N$i (sqrtb(N$i)).

definition: forall X (squareLEb(X) <-> exists N$i (N$i=X and N$i >= 1 and N$i <= b and N$i*N$i <= b)).

inductive-lemma: forall N$i (N$i >= 1 -> squareLEb(N$i)).
