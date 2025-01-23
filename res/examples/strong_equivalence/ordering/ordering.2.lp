sort(X,Y) :- p(X); p(Y); #false : p(Z), X < Z, Z < Y.
