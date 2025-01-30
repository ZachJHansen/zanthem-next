parent_living(X) :- father(Y,X), living(Y).
parent_living(X) :- mother(Y,X), living(Y).
rphan(X) :- living(X), not parent_living(X).
