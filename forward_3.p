
%%%%%%%
tff(type, type, object: $tType).
tff(type, type, f__integer__: ($int) > object).
tff(type, type, f__symbolic__: ($i) > object).
tff(type, type, c__infimum__: object).
tff(type, type, c__supremum__: object).
tff(type, type, p__is_integer__: (object) > $o).
tff(type, type, p__is_symbolic__: (object) > $o).
tff(type, type, p__less_equal__: (object * object) > $o).
tff(type, type, p__less__: (object * object) > $o).
tff(type, type, p__greater_equal__: (object * object) > $o).
tff(type, type, p__greater__: (object * object) > $o).
%%%%%%%
tff(axiom, axiom, ![X: object]: (p__is_integer__(X) <=> (?[N: $int]: (X = f__integer__(N))))).
tff(axiom, axiom, ![X1: object]: (p__is_symbolic__(X1) <=> (?[X2: $i]: (X1 = f__symbolic__(X2))))).
tff(axiom, axiom, ![X: object]: ((X = c__infimum__) | p__is_integer__(X) | p__is_symbolic__(X) | (X = c__supremum__))).
tff(axiom, axiom, ![N1: $int, N2: $int]: ((f__integer__(N1) = f__integer__(N2)) <=> (N1 = N2))).
tff(axiom, axiom, ![S1: $i, S2: $i]: ((f__symbolic__(S1) = f__symbolic__(S2)) <=> (S1 = S2))).
tff(axiom, axiom, ![N1: $int, N2: $int]: (p__less_equal__(f__integer__(N1), f__integer__(N2)) <=> $lesseq(N1, N2))).
tff(axiom, axiom, ![X1: object, X2: object]: ((p__less_equal__(X1, X2) & p__less_equal__(X2, X1)) => (X1 = X2))).
tff(axiom, axiom, ![X1: object, X2: object, X3: object]: ((p__less_equal__(X1, X2) & p__less_equal__(X2, X3)) => p__less_equal__(X1, X3))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__less_equal__(X1, X2) | p__less_equal__(X2, X1))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__less__(X1, X2) <=> (p__less_equal__(X1, X2) & (X1 != X2)))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__greater_equal__(X1, X2) <=> p__less_equal__(X2, X1))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__greater__(X1, X2) <=> (p__less_equal__(X2, X1) & (X1 != X2)))).
tff(axiom, axiom, ![N: $int]: p__less__(c__infimum__, f__integer__(N))).
tff(axiom, axiom, ![N: $int, S: $i]: p__less__(f__integer__(N), f__symbolic__(S))).
tff(axiom, axiom, ![S: $i]: p__less__(f__symbolic__(S), c__supremum__)).
%%%%%%%

%%%% Predicates %%%%

tff(predicate_0, type, edge: (object * object) > $o).
tff(predicate_1, type, color: (object) > $o).
tff(predicate_2, type, color: (object * object) > $o).
tff(predicate_3, type, vertex: (object) > $o).
tff(predicate_4, type, aux: (object) > $o).
%%%% Functions %%%%

%%%% Axioms %%%%
tff(statement, axiom, ![Xg: object, Z1g: object, Z2g: object]: (?[Zg: object, Z2g: object]: (Zg = Xg & Z2g = Z1g & color(Zg, Z2g)) & ?[Zg: object, Z1g: object]: (Zg = Xg & Z1g = Z2g & color(Zg, Z1g)) & ?[Zg: object, Z3g: object]: (Zg = Z1g & Z3g = Z2g & Zg != Z3g) => $false)).

tff(statement, axiom, ![Xg: object]: (?[Zg: object]: (Zg = Xg & vertex(Zg)) & ?[Zg: object]: (Zg = Xg & ~aux(Zg)) => $false)).

tff(statement, axiom, ![Xg: object, Yg: object, Zg: object]: (?[Zg: object, Z1g: object]: (Zg = Xg & Z1g = Yg & edge(Zg, Z1g)) & ?[Z1g: object, Z2g: object]: (Z1g = Xg & Z2g = Zg & color(Z1g, Z2g)) & ?[Z1g: object, Z2g: object]: (Z1g = Yg & Z2g = Zg & color(Z1g, Z2g)) => $false)).

tff(statement, axiom, ![V1g: object, V2g: object]: (color(V1g, V2g) <=> ?[Xg: object, Zg: object]: (V1g = Xg & V2g = Zg & (?[Zg: object]: (Zg = Xg & vertex(Zg)) & ?[Z1g: object]: (Z1g = Zg & color(Z1g))) & ~~color(V1g, V2g)))).

tff(statement, axiom, ![V1g: object]: (aux(V1g) <=> ?[Xg: object, Zg: object]: (V1g = Xg & (?[Zg: object]: (Zg = Xg & vertex(Zg)) & ?[Z1g: object]: (Z1g = Zg & color(Z1g)) & ?[Z1g: object, Z2g: object]: (Z1g = Xg & Z2g = Zg & color(Z1g, Z2g)))))).

tff(statement, axiom, ![Xg: object, Yg: object]: (edge(Xg, Yg) => (vertex(Xg) & vertex(Yg)))).

tff(statement, axiom, ![Xg: object, Zg: object]: (color(Xg, Zg) => (vertex(Xg) & color(Zg)))).

tff(statement, axiom, ![Xg: object]: (vertex(Xg) => ?[Zg: object]: (color(Xg, Zg)))).

%%%% Conjecture %%%%
tff(statement, conjecture, ![Xg: object, Z1g: object, Z2g: object]: (color(Xg, Z1g) & color(Xg, Z2g) => Z1g = Z2g)).
