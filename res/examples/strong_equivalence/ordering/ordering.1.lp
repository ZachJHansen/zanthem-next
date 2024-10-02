order(X,Y) :- p(X); p(Y); not p(Z) : p(Z), X < Z, Z < Y.
