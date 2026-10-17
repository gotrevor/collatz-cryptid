from itertools import combinations
H=[0, -2, 5, 7, 0, 9, 10, 6, 0, 14, 13, 17, 0, 17, 26, 22, 0, 30, 27, 25, 0, 31, 26, 38]
W=[0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, -1, 0, 0, -1, 0, 1, 0, 0, 1, -1]
q,p=24,32
neg=[r for r in range(q) if W[r]<0]
def need(src,S):
    worst=0
    for r in src:
        for t in range(q):
            a=(p*t+H[r])%q
            c=min(c for c in range(q) if (a+c)%q in S)
            worst=max(worst,c)
    return worst
R=[r for r in range(q) if r%4]
for k in range(1,4):
    for S in combinations(neg,k):
        print(S, "entry-all",need(range(q),S),"entry-R",need(R,S),"closure-only",need(S,S))
