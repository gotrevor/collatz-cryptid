import sys
def find(p,q,g,w,d,m,E,T=None):
    T=T or q
    R=set(range(q))
    while True:
        phi={r:0 for r in R}
        cap=q*(m*max(abs(v) for v in w)+1)+1
        bad=set()
        for it in range(5000):
            ch=False
            for r in R:
                worst=None
                for t in range(T):
                    best=None
                    for c in range(d+1):
                        r2=(p*t+g[r]+c)%q
                        if r2 in R:
                            v=m*w[r]+1+phi[r2]
                            best=v if best is None else min(best,v)
                    if best is None: best=cap
                    worst=best if worst is None else max(worst,best)
                nv=max(0,worst)
                if nv>phi[r] and phi[r]<cap:
                    phi[r]=min(nv,cap); ch=True
            if not ch: break
        bad={r for r in R if phi[r]>=cap}
        if not bad: break
        R-=bad
        if not R: return None
    # entry check
    for r in range(q):
        if E(r):
            for t in range(T):
                if not any((p*t+g[r]+c)%q in R for c in range(d+1)): return ('entryfail',sorted(R),phi)
    return sorted(R),[phi.get(r,0) for r in range(q)]
H=[0, -2, 5, 7, 0, 9, 10, 6, 0, 14, 13, 17, 0, 17, 26, 22, 0, 30, 27, 25, 0, 31, 26, 38]
W=[0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, -1, 0, 0, -1, 0, 1, 0, 0, 1, -1]
for d in range(5,14):
    for m in [1,2,3,4,6]:
        r=find(32,24,H,W,d,m,lambda r:r%4!=0)
        if r and r[0]!='entryfail':
            print(d,m,r); break
    else: print(d,'none')
