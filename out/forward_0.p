tff(type, type, general: $tType).
tff(type, type, symbol: $tType).
tff(type, type, f__integer__: ($int) > general).
tff(type, type, f__symbolic__: (symbol) > general).
tff(type, type, c__infimum__: general).
tff(type, type, c__supremum__: general).
tff(type, type, p__is_integer__: (general) > $o).
tff(type, type, p__is_symbolic__: (general) > $o).
tff(type, type, p__less_equal__: (general * general) > $o).
tff(type, type, p__less__: (general * general) > $o).
tff(type, type, p__greater_equal__: (general * general) > $o).
tff(type, type, p__greater__: (general * general) > $o).
tff(axiom, axiom, ![X: general]: (p__is_integer__(X) <=> (?[N: $int]: (X = f__integer__(N))))).
tff(axiom, axiom, ![X1: general]: (p__is_symbolic__(X1) <=> (?[X2: symbol]: (X1 = f__symbolic__(X2))))).
tff(axiom, axiom, ![X: general]: ((X = c__infimum__) | p__is_integer__(X) | p__is_symbolic__(X) | (X = c__supremum__))).
tff(axiom, axiom, ![N1: $int, N2: $int]: ((f__integer__(N1) = f__integer__(N2)) <=> (N1 = N2))).
tff(axiom, axiom, ![S1: symbol, S2: symbol]: ((f__symbolic__(S1) = f__symbolic__(S2)) <=> (S1 = S2))).
tff(axiom, axiom, ![N1: $int, N2: $int]: (p__less_equal__(f__integer__(N1), f__integer__(N2)) <=> $lesseq(N1, N2))).
tff(axiom, axiom, ![X1: general, X2: general]: ((p__less_equal__(X1, X2) & p__less_equal__(X2, X1)) => (X1 = X2))).
tff(axiom, axiom, ![X1: general, X2: general, X3: general]: ((p__less_equal__(X1, X2) & p__less_equal__(X2, X3)) => p__less_equal__(X1, X3))).
tff(axiom, axiom, ![X1: general, X2: general]: (p__less_equal__(X1, X2) | p__less_equal__(X2, X1))).
tff(axiom, axiom, ![X1: general, X2: general]: (p__less__(X1, X2) <=> (p__less_equal__(X1, X2) & (X1 != X2)))).
tff(axiom, axiom, ![X1: general, X2: general]: (p__greater_equal__(X1, X2) <=> p__less_equal__(X2, X1))).
tff(axiom, axiom, ![X1: general, X2: general]: (p__greater__(X1, X2) <=> (p__less_equal__(X2, X1) & (X1 != X2)))).
tff(axiom, axiom, ![N: $int]: p__less__(c__infimum__, f__integer__(N))).
tff(axiom, axiom, ![N: $int, S: symbol]: p__less__(f__integer__(N), f__symbolic__(S))).
tff(axiom, axiom, ![S: symbol]: p__less__(f__symbolic__(S), c__supremum__)).
tff(predicate_0, type, hsort: (general * general) > $o).
tff(predicate_1, type, tsort: (general * general) > $o).
tff(predicate_2, type, hp: (general) > $o).
tff(predicate_3, type, tp: (general) > $o).
tff(transition_axiom_0, axiom, ![X1_g: general, X2_g: general]: (hsort(X1_g, X2_g) => tsort(X1_g, X2_g))).
tff(transition_axiom_1, axiom, ![X1_g: general]: (hp(X1_g) => tp(X1_g))).
tff(left_0, axiom, ![V2_g: general, X_g: general, Y_g: general]: ((![Z_g: general]: (((V2_g = Y_g & hp(X_g)) & hp(Y_g)) & ((((hp(Z_g) & p__less__(X_g, Z_g)) & p__less__(Z_g, Y_g)) => (~tp(Z_g))) & (((tp(Z_g) & p__less__(X_g, Z_g)) & p__less__(Z_g, Y_g)) => (~tp(Z_g))))) => hsort(X_g, V2_g)) & (![Z_g: general]: (((V2_g = Y_g & tp(X_g)) & tp(Y_g)) & (((tp(Z_g) & p__less__(X_g, Z_g)) & p__less__(Z_g, Y_g)) => (~tp(Z_g)))) => tsort(X_g, V2_g)))).
tff(right_0, conjecture, ![X_g: general, Y_g: general, Z_g: general]: ((((hp(X_g) & hp(Y_g)) & ((((hp(Z_g) & p__less__(X_g, Z_g)) & p__less__(Z_g, Y_g)) => $false) & (((tp(Z_g) & p__less__(X_g, Z_g)) & p__less__(Z_g, Y_g)) => $false))) => hsort(X_g, Y_g)) & (((tp(X_g) & tp(Y_g)) & (((tp(Z_g) & p__less__(X_g, Z_g)) & p__less__(Z_g, Y_g)) => $false)) => tsort(X_g, Y_g)))).
