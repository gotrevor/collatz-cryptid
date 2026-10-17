# Shape-return growth screen.  For each TM: run Quick_Sim's simulator (prover on, recursive),
# collect chain-tape configs with the head at a tape edge, group by shape (symbols, state, dir),
# and for each shape with enough occurrences compute per-occurrence ratios of the max exponent.
# Output JSON per machine: best shape's geometric-mean ratio over the late half, its spread, count.
import sys, runpy, io, contextlib, math, json, signal
from fractions import Fraction
def analyze(code, tm, loops, secs):
    sys.argv = ['Quick_Sim.py', '--manual', '-q', '-r', tm]
    signal.alarm(secs)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            g = runpy.run_path(code + '/Quick_Sim.py', run_name='__main__')
        sim = g['sim']
        from Macro import Turing_Machine
        shapes = {}
        for i in range(loops):
            if sim.op_state != Turing_Machine.RUNNING: break
            with contextlib.redirect_stdout(io.StringIO()):
                sim.step()
            L, R = sim.tape.tape
            if len(L) != 1 and len(R) != 1: continue
            try:
                ex = [int(b.num) for side in (L, R) for b in side[1:]]
                key = (str(sim.state), sim.tape.dir, tuple(str(b.symbol) for b in L), tuple(str(b.symbol) for b in R))
            except Exception:
                continue
            if not ex: continue
            m = max(ex)
            if m < 2: continue
            shapes.setdefault(key, []).append(m)
        state = str(sim.op_state)
    except TimeoutError:
        state = 'TIMEOUT'
    finally:
        signal.alarm(0)
    best = None
    for key, ms in shapes.items():
        if len(ms) < 12: continue
        late = ms[len(ms)//2:]
        lr = [math.log(b/a) for a, b in zip(late, late[1:]) if a > 0 and b > 0]
        if not lr: continue
        mean = sum(lr)/len(lr); sd = (sum((x-mean)**2 for x in lr)/len(lr))**0.5
        cand = dict(ratio=math.exp(mean), sd=sd, n=len(ms), maxexp=ms[-1], shape=' '.join(key[2])+f' {key[0]}{"><"[key[1]==0]} '+' '.join(key[3]))
        if best is None or cand['ratio'] > best['ratio']: best = cand
    if best:
        f = Fraction(best['ratio']).limit_denominator(6)
        best['near'] = f'{f.numerator}/{f.denominator}'; best['off'] = abs(best['ratio'] - float(f))
    return dict(tm=tm, state=state, nshapes=len(shapes), best=best)
def _alarm(*a): raise TimeoutError
if __name__ == '__main__':
    code, loops, secs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    sys.path.insert(0, code); signal.signal(signal.SIGALRM, _alarm)
    tms = sys.argv[4:]
    for tm in tms: print(json.dumps(analyze(code, tm, loops, secs), default=str), flush=True)
