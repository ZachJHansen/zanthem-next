lemma: forall X N1$i N2$i ( (N1$i > 1 and N2$i > 1 and X = N1$i * N2$i) -> (N1$i <= X and N2$i <= X) ).
lemma: forall V1 (prime(V1) <- exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite_2(Z))))).
lemma: forall V1 (prime(V1) -> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite_2(Z))))).
