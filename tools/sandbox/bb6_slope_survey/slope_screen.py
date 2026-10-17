# Growth-base screen: time t_w at which tape width first reaches w; fit log t_w ~ w log(lambda)
# over the last half of records.  Positional counters give lambda>1; polynomial machines give ~1.
import sys, math, json
from multiprocessing import Pool
def parse(tm):
    rows=tm.split('_'); T={}
    for s,row in enumerate(rows):
        for sym in (0,1):
            t=row[3*sym:3*sym+3]
            if t[0]=='-': continue
            T[(s,sym)]=(int(t[0]), 1 if t[1]=='R' else -1, ord(t[2])-65)
    return T
def run(args):
    tm,N=args; T=parse(tm)
    tape=bytearray(2*N+3); p=N+1; lo=hi=p; s=0; rec=[]
    for t in range(N):
        tr=T.get((s,tape[p]))
        if tr is None: return tm,'HALT',t,None,rec[-3:]
        tape[p],d,s=tr; p+=d
        if p<lo: lo=p; rec.append(t)
        elif p>hi: hi=p; rec.append(t)
    # fit on last half of width records (records with t>=1000)
    pts=[(i,math.log(t)) for i,t in enumerate(rec) if t>=1000]
    pts=pts[len(pts)//2:]
    if len(pts)<6: return tm,'FEW',N,None,len(rec)
    n=len(pts); mx=sum(x for x,_ in pts)/n; my=sum(y for _,y in pts)/n
    b=sum((x-mx)*(y-my) for x,y in pts)/sum((x-mx)**2 for x,_ in pts)
    # local slope stability: fit on last quarter too
    q=pts[len(pts)//2:]; m2=sum(x for x,_ in q)/len(q); y2=sum(y for _,y in q)/len(q)
    b2=sum((x-m2)*(y-y2) for x,y in q)/max(1e-9,sum((x-m2)**2 for x,_ in q))
    return tm,'RUN',N,(math.exp(b),math.exp(b2)),len(rec)
if __name__=='__main__':
    N=int(sys.argv[1]); tms=[l.split()[0] for l in open(sys.argv[2]) if l.strip()]
    with Pool() as P:
        for r in P.imap_unordered(run,[(t,N) for t in tms]): print(json.dumps(r),flush=True)
