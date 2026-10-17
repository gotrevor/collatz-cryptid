from fractions import Fraction
H=[0, -2, 5, 7, 0, 9, 10, 6, 0, 14, 13, 17, 0, 17, 26, 22, 0, 30, 27, 25, 0, 31, 26, 38]
W=[0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, -1, 0, 0, -1, 0, 1, 0, 0, 1, -1]
def game(p,q,H,W,d,T,R,iters=3000):
    V=[0]*q
    for k in range(iters):
        V=[W[r]+max(min(V[(p*t+H[r]+c)%q] for c in range(d+1)) for t in range(T)) for r in range(q)]
    return [v/iters for v in V]
R=[r for r in range(24) if r%4]
for d in range(0,15):
    v=game(32,24,H,W,d,3,R)
    # entry: from R residues, worst over t of best c of value of next
    ent=max(max(min(v[(32*t+H[r]+c)%24] for c in range(d+1)) for t in range(3)) for r in R)
    print(d, round(max(v[r] for r in R),3), round(ent,3))
