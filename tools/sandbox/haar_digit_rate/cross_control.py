# lambda_n(a) = 2 sum_{e = a mod 2} pi(e) lambda_{n-1}((b a - e)/2), exact rationals over integers a (mod 2^n)
import sys
from fractions import Fraction as F
def lam(b, p, n, a0=1):
    pi = {}
    for x in range(3):
        for y in range(3): pi[x-y] = pi.get(x-y, 0) + p[x]*p[y]
    cur = {a0: 1.0}
    for j in range(n):
        m = n - j - 1; M = 1 << m if m < 62 else None
        nxt = {}
        for d, w in cur.items():
            for e in (-2,-1,0,1,2):
                if (e - d) % 2: continue
                c = (b*d - e)//2
                if M: c %= M
                nxt[c] = nxt.get(c, 0.0) + w*2*pi[e]
        cur = nxt
    return sum(cur.values())
for b in (1, 3, 5):
    print(b, [round(lam(b, [1/3,1/3,1/3], n), 4) for n in (8, 12, 16, 18)])
