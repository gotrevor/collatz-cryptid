# Fast checker: compare the tape tree at every Goodstein boundary with a symbolic hereditary-base
# reference (number = descending list of exponent-trees; no big integers), so big seeds stay cheap.
import json, sys; sys.setrecursionlimit(100000)
def sym(n, b):                       # n in hereditary base b as a descending tuple of exponent-trees
    out, e = [], 0
    while n:
        n, r = divmod(n, b); out += [sym(e, b)] * r; e += 1
    return tuple(reversed(out))
def less1(t, b):                     # t - 1 in hereditary base b (t != 0)
    *rest, last = t
    if last == (): return tuple(rest)
    e1 = less1(last, b)              # b^E - 1 = (b-1) b^(E-1) + (b^(E-1) - 1)
    return tuple(rest) + (e1,) * (b - 1) + less1((e1,), b)
def levels(t, lvl=1, out=None):
    out = [] if out is None else out
    for e in t: out.append(lvl); levels(e, lvl + 1, out)
    return out
M = json.load(open(sys.argv[1])); T = M['table']; seed = M['seed']; cap = int(sys.argv[2])
tape, head, state, steps = {}, 0, 'INIT', 0
ref, base, k, prev = sym(seed, 2), 2, 0, None
while steps < cap:
    sym_ = tape.get(head, '_')
    if state == 'GSTEP_BUMP' and prev != 'GSTEP_BUMP' and steps > 0:
        ks = sorted(x for x, v in tape.items() if v != '_'); s = ''.join(tape.get(x, '_') for x in range(ks[0], ks[-1] + 1))
        b = s[:s.index('[')].count('b'); depths = [len(x) for x in s[s.index(']') + 1:].split('P')[1:]]
        assert b == base and depths == levels(ref), ('MISMATCH', k, b, base)
        base += 1; k += 1; ref = less1(ref, base)
    prev = state
    if sym_ not in T[state]:
        assert ref == (), ('halted early', k)
        print(f'seed {seed}: HALTED after {steps} TM steps, {k} Goodstein steps'); break
    w, m, nx = T[state][sym_]; tape[head] = w; head += 1 if m == 'R' else -1; state = nx; steps += 1
else:
    print(f'seed {seed}: running at {steps} TM steps; {k-1} Goodstein steps match the symbolic reference; base {base-1}; tree has {len(levels(ref))} nodes')
