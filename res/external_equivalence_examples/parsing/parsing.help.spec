definition[def_of_q]: forall X (q(X) <-> exists Y edge(X,Y)).
lemma(forward): q(5).
definition[def_of_g]: forall X ( g(X) <-> exists Y (q(X) and edge(Y,X)) ).
lemma: g(n) or q(n).
inductive-lemma(backward): forall N$i ( N$i >= 0 -> exists Y (g(N$i) or edge(N$i, Y)) ).
