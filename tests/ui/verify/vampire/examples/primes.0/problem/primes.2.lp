composite(X*Y) :- X = 2..b, Y = 2..b.
prime(X) :- X = a..b, not composite(X).