composite(X*Y) :- X > 1, Y > 1.
prime(X) :- X = a..b, not composite(X).
