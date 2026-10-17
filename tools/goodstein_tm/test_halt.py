import json, sys; sys.setrecursionlimit(100000)
from check import value, sub1, hered
def bump(n, b, c):
    r, e = 0, 0
    while n:
        n, d = divmod(n, b)
        if d: r += d * c ** bump(e, b, c)
        e += 1
    return r
M = json.load(open(sys.argv[1])); T = M['table']; seed = M['seed']; cap = int(sys.argv[2])
tape, head, state, steps = {}, 0, 'INIT', 0
g, base, k, prev = seed, 2, 0, None
while steps < cap:
    sym = tape.get(head, '_')
    if state == 'GSTEP_BUMP' and prev != 'GSTEP_BUMP' and steps > 0:
        ks = sorted(x for x, v in tape.items() if v != '_'); s = ''.join(tape.get(x, '_') for x in range(ks[0], ks[-1] + 1))
        b = s[:s.index('[')].count('b'); depths = [len(x) for x in s[s.index(']') + 1:].split('P')[1:]]
        if k == 0: assert depths == hered(seed, 2) and b == 2
        else:
            assert b == base and value(depths, base) == g, ('MISMATCH', k, b, base)
        base += 1; k += 1; g = bump(g, base - 1, base) - 1
    prev = state
    if sym not in T[state]:
        assert g == 0, ('halted early', g)
        print(f'seed {seed}: HALTED after {steps} TM steps, {k} Goodstein steps (reference: sequence hits 0 at step {k})'); break
    w, m, nx = T[state][sym]; tape[head] = w; head += 1 if m == 'R' else -1; state = nx; steps += 1
else:
    print(f'seed {seed}: still running after {steps} TM steps; {k-1} Goodstein steps all match the big-int reference; base {base-1}, current value has {len(str(g))} digits')
