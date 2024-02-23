sqrt_b(Z) :- Z = 1..b, Z*Z <= b, (Z+1)*(Z+1) > b.
composite(X*Y) :- sqrt_b(Z), X = 2..Z, Y = 2..b.
prime(X) :- X = a..b, not composite(X).
