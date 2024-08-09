assumption: n > 5 -> t.
assumption(backward): forall X (edge(X, n) <-> t).
spec[spec_1]: reachable(5,6).
spec(forward)[spec_2]: forall X Y ( reachable(X,Y) <-> edge(X,Y) ).
