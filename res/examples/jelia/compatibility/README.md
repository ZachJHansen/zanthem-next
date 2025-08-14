% p :- X = 1..3 :: q(X).

anthem verify --equivalence strong p.{1.lp,2.lp} -t 120 -m 4

% order(X, Y ) :- p(X); p(Y ); #false :: p(Z), X < Z, Z < Y

anthem verify --equivalence strong p.{3.lp,4.lp} -t 120 -m 4

% p :- t :: q

anthem verify --equivalence strong p.{5.lp,6.lp} -t 120 -m 4

% p(Y) :- t(X, Y) :: q(Y); r(X)

anthem verify --equivalence strong p.{7.lp,8.lp} -t 120 -m 4

% p(Y) :- 2 < 1 :: q(Y); r(Y)

anthem verify --equivalence strong p.{9.lp,10.lp} -t 120 -m 4
