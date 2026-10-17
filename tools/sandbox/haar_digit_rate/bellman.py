# Exact Haar-mean optimal digit cost A_N = 2^-N sum_{x mod 2^N} V_N(x), base 3/2 canonical digits.
# V_{N+1}(2m) = min(V_N(3m), 2 + V_N(3m+1)),  V_{N+1}(2m+1) = 1 + V_N(3m+2)   (args mod 2^N).
import sys, numpy as np
Nmax = int(sys.argv[1])
V = np.zeros(1, dtype=np.int16); prev = 0.0
for N in range(Nmax):
    M = 1 << N
    m = np.arange(M, dtype=np.int64)
    W = np.empty(2 * M, dtype=np.int16)
    W[0::2] = np.minimum(V[(3 * m) % M], 2 + V[(3 * m + 1) % M])
    W[1::2] = 1 + V[(3 * m + 2) % M]
    V = W; tot = int(V.sum(dtype=np.int64)); A = tot / (2 * M)
    print(N + 1, tot, f'A/N={A/(N+1):.6f}', f'dA={A-prev:.6f}', flush=True); prev = A
