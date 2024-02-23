Premises:
forall V1 (composite_2(V1) <-> exists K$i K1$i (V1 = K1$i * K$i and 2 <= K1$i <= n and 2 <= K$i <= n))
forall V1 (prime(V1) <-> exists K$i (2 <= K$i <= n and V1 = K$i and not composite_2(V1)))
forall V1 (composite_1(V1) <-> exists I1$i J1$i (V1 = I1$i * J1$i and I1$i > 1 and J1$i > 1))

Conclusions:
forall M$i N$i (M$i >= 1 and N$i >= 1 -> M$i * N$i <= M$i)
forall V1 (prime(V1) <-> exists K$i (2 <= K$i <= n and V1 = K$i and not composite_1(V1)))











Premises:
forall X (composite_1(X) <-> exists N1, N2 (N1 > 1 and N2 > 1 and X = N1 * N2))
forall X (composite_2(X) <-> exists N1, N2 (2 <= N1 and N1 <= n and 2 <= N2 and N2 <= n and X = N1 * N2))
forall X (prime(X) <-> exists N (2 <= N and N <= n and not composite_2(N) and X = N))

Conclusions:
forall N1, N2, N3 (N2 > 1 and N3 > 1 and N1 = N2 * N3 -> N2 <= N1 and N3 <= N1) in 0.009 seconds
forall X (prime(X) <- exists N1 (exists N2 (N2 = n and 2 <= N1 and N1 <= N2) and not composite_1(N1) and X = N1)) in 0.055 seconds
forall X (prime(X) <-> exists N1 (exists N2 (N2 = n and 2 <= N1 and N1 <= N2) and not composite_1(N1) and X = N1)) in 1.287 seconds

Premises:
forall X (composite_1(X) <-> exists N1, N2 (N1 > 1 and N2 > 1 and X = N1 * N2))
forall X (composite_2(X) <-> exists N1, N2 (2 <= N1 and N1 <= n and 2 <= N2 and N2 <= n and X = N1 * N2))
forall X (prime(X) <-> exists N1 (exists N2 (N2 = n and 2 <= N1 and N1 <= N2) and not composite_1(N1) and X = N1))
   
Conclusions:
forall N1, N2, N3 (N2 > 1 and N3 > 1 and N1 = N2 * N3 -> N2 <= N1 and N3 <= N1) in 0.021 seconds
forall X (prime(X) <- exists N1 (exists N2 (N2 = n and 2 <= N1 and N1 <= N2) and not composite_1(N1) and X = N1)) in 0.009 seconds
forall X (prime(X) <-> exists N (2 <= N and N <= n and not composite_2(N) and X = N)) in 78.611 seconds



