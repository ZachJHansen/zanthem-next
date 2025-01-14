{asg(V, C)} :- vtx(V), col(C).
:- asg(V, C1), asg(V, C2), C1 != C2.
:- not asg(V, C) : col(C); vtx(V).
:- asg(V1, C), asg(V2, C), edge(V1, V2).
