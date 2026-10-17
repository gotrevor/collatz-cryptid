# Simulate tm.json; at every Goodstein-step boundary decode WORK and compare with two references:
# (1) the hydra process on level sequences, (2) for canonical trees, big-integer Goodstein.
import json, sys
M = json.load(open('tm.json')); T = M['table']
def run(max_steps, tape=None, head=0, state='INIT', on_event=None):
    tape = dict(tape or {}); n = 0
    while n < max_steps:
        sym = tape.get(head, '_')
        if state in ('GSTEP_BUMP', 'BEEP') and on_event and prev != state:
            on_event(state, tape, n)
        prev = state
        w, m, nx = T[state][sym]
        tape[head] = w; head += 1 if m == 'R' else -1; state = nx; n += 1
    return n
prev = None
def regions(tape):
    ks = sorted(k for k, v in tape.items() if v != '_')
    s = ''.join(tape.get(k, '_') for k in range(ks[0], ks[-1] + 1))
    base = s[:s.index('[')]; seed = s[s.index('[')+1:s.index(']')]; work = s[s.index(']')+1:]
    depths = [len(x) for x in work.split('P')[1:]]
    return base.count('b'), seed, depths, work
def decode_seed(seed):                      # reference decoding with clamping
    d = [1]
    for c in seed:
        if c == 'N': d.append(d[-1] + 1)
        elif c == 'u' and len(d) > 1: d[-1] = max(1, d[-1] - 1)
    return d
def sub1(depths, b):                        # reference hydra step on level sequences
    d = list(depths)
    while True:
        L = d.pop(); k = L - 1
        if k == 0: return d
        i = max(j for j in range(len(d)) if d[j] == k)
        blk = d[i:]; d += blk * (b - 1)
def value(depths, b):                       # value of tree in base b (top-level sum)
    def parse(i, lvl):
        terms = []
        while i < len(depths) and depths[i] == lvl:
            e, i = parse(i + 1, lvl + 1); terms.append(b ** e)
        return sum(terms), i
    v, i = parse(0, 1); assert i == len(depths); return v
def hered(n, b):                            # canonical hereditary base-b tree of n as level sequence
    out = []
    def rec(n, lvl):
        e = 0; terms = []
        while n:
            n, r = divmod(n, b); terms.append((e, r)); e += 1
        for e, r in reversed(terms):
            for _ in range(r): out.append(lvl); rec(e, lvl + 1)
    rec(n, 1); return out
