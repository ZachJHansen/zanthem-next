spec: forall X (
    prime(X) <-> 
        exists N$ (
            X = N$ and a <= N$ <= b and  
            not exists D$ M$ (1 < D$ < N$ and M$*D$ = N$)
        )
).
