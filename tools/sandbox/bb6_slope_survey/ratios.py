import sys, json, math, collections
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, sys.argv[1].rsplit('/',1)[0] if False else '.')
import shape_growth as S, signal
signal.signal(signal.SIGALRM, S._alarm)
code, tm = sys.argv[1], sys.argv[2]; NL = int(sys.argv[3]) if len(sys.argv)>3 else 20000
# re-run, keeping raw per-shape sequences
import runpy, io, contextlib
sys.argv = ['Quick_Sim.py', '--manual', '-q', '-r', tm]
with contextlib.redirect_stdout(io.StringIO()):
    g = runpy.run_path(code + '/Quick_Sim.py', run_name='__main__')
sim = g['sim']; shapes = {}
for i in range(NL):
    if str(sim.op_state) != 'Running': break
    with contextlib.redirect_stdout(io.StringIO()): sim.step()
    L, R = sim.tape.tape
    if len(L) != 1 and len(R) != 1: continue
    try: ex = [int(b.num) for side in (L, R) for b in side[1:]]
    except Exception: continue
    key = (str(sim.state), sim.tape.dir, tuple(str(b.symbol) for b in L), tuple(str(b.symbol) for b in R))
    shapes.setdefault(key, []).append(ex)
for key, vs in sorted(shapes.items(), key=lambda kv: -len(kv[1]))[:4]:
    ms = [max(v) for v in vs]; late = ms[len(ms)//2:]
    rs = [b/a for a, b in zip(late, late[1:]) if a > 1000]
    c = collections.Counter(round(r, 4) for r in rs)
    print(len(vs), key[0], key[2], key[3]); print('   ratios', c.most_common(8))
