% types
tff(type_general, type, general: $tType).
% casting integer to general
tff(cast_int, type, to_general: $int > general).
% casting axiom
tff(unique_cast, axiom,
  ![X: $int, Y: $int]: ((X != Y) => (to_general(X) != to_general(Y)))).
% infimum and supremum
tff(type_infimum, type, infimum: general).
tff(type_supremum, type, supremum: general).
% comparisons on general
tff(less_equal, type,
  lesseq: (general * general) > $o).
tff(less, type,
  less: (general * general) > $o).
tff(greater_equal, type,
  greatereq: (general * general) > $o).
tff(greater, type,
  greater: (general * general) > $o).
% comparison axioms
tff(lesseq_int, axiom,
  ![X: $int, Y: $int]: ($lesseq(X,Y) <=> lesseq(to_general(X),to_general(Y)))).
tff(lesseq_anti_symmetry, axiom,
  ![X: general, Y: general]: ((lesseq(X,Y) & lesseq(Y,X)) => (X = Y))).
tff(lesseq_transitivity, axiom,
  ![X: general, Y: general, Z: general]: ((lesseq(X,Y) & lesseq(Y,Z)) => lesseq(X,Z))).
tff(lesseq_total, axiom,
  ![X: general, Y: general]: (lesseq(X,Y) | lesseq(Y,X))).
tff(less_to_lesseq, axiom,
  ![X: general, Y: general]: (less(X,Y) <=> (lesseq(X,Y) & (X != Y)))).
tff(greatereq_to_lesseq, axiom,
  ![X: general, Y: general]: (greatereq(X,Y) <=> lesseq(Y,X))).
tff(greater_to_lesseq, axiom,
  ![X: general, Y: general]: (greater(X,Y) <=> (lesseq(Y,X) & (X != Y)))).
tff(less_infimum, axiom,
  ![X: general]: less(infimum,X)).
tff(less_supremum, axiom,
  ![X: general]: less(X,supremum)).
