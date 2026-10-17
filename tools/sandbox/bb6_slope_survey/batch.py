# Batch shape-return slope survey.  Per machine: top shapes by edge-occurrence count, the ratio
# clusters (rounded 4dp) of the max exponent between consecutive occurrences (late half, exps > 1000).
import sys, json, runpy, io, contextlib, collections, signal
from multiprocessing import Pool
CODE = sys.argv[1]; LOOPS = int(sys.argv[2]); SECS = int(sys.argv[3])
def _alarm(*a): raise TimeoutError
def one(tm):
    sys.path.insert(0, CODE); signal.signal(signal.SIGALRM, _alarm); signal.alarm(SECS)
    shapes = {}; st = '?'; loops = 0
    try:
        sys.argv = ['Quick_Sim.py', '--manual', '-q', '-r', tm]
        with contextlib.redirect_stdout(io.StringIO()):
            g = runpy.run_path(CODE + '/Quick_Sim.py', run_name='__main__')
        sim = g['sim']
        for loops in range(LOOPS):
            if str(sim.op_state) != 'Running': break
            with contextlib.redirect_stdout(io.StringIO()): sim.step()
            L, R = sim.tape.tape
            if len(L) != 1 and len(R) != 1: continue
            try: m = max([int(b.num) for side in (L, R) for b in side[1:]] or [0])
            except Exception: continue
            key = str(sim.state) + '|' + str(sim.tape.dir) + '|' + ' '.join(str(b.symbol) for b in L) + '|' + ' '.join(str(b.symbol) for b in R)
            shapes.setdefault(key, []).append(m)
        st = str(sim.op_state)
    except TimeoutError: st = 'TIMEOUT'
    except Exception as e: st = 'ERR ' + type(e).__name__
    finally: signal.alarm(0)
    top = []
    for key, ms in sorted(shapes.items(), key=lambda kv: -len(kv[1]))[:5]:
        late = ms[len(ms)//2:]
        rs = [b/a for a, b in zip(late, late[1:]) if a > 1000]
        c = collections.Counter(round(r, 4) for r in rs)
        top.append(dict(n=len(ms), nr=len(rs), clusters=c.most_common(5), maxlog10=len(str(ms[-1])) if ms else 0))
    return dict(tm=tm, state=st, loops=loops, nshapes=len(shapes), top=top)
if __name__ == '__main__':
    tms = [l.split()[0] for l in open(sys.argv[4]) if l.strip()]
    with Pool(12, maxtasksperchild=10) as P:
        for r in P.imap_unordered(one, tms): print(json.dumps(r), flush=True)
