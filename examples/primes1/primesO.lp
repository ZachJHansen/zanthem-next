sqrtb(I) :- I = 1..b, I*I <= b, (I+1)*(I+1) > b.
composite(I*J) :- sqrtb(M), I = 2..b, J = 2..b.
prime(I) :- I = a..b, not composite(I).