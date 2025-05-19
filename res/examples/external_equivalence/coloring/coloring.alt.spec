assumption: forall X Y (edge(X,Y) -> vertex(X) and vertex(Y)).
spec: forall V (vertex(V) -> exists C (color(C) and color(V, C))).
