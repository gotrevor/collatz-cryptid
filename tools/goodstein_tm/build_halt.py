# Goodstein HALTING Turing machine: runs the Goodstein sequence from a fixed seed n, halts at 0.
# Tape: [BASE b..b] '[' ']' [WORK: hereditary base-b tree as level sequence, nodes 'P' d^depth].
# Each Goodstein step: b += 1, then subtract 1 in hereditary base b (rightmost-hydra chop with b-1 copies).
import json, sys
n = int(sys.argv[1])
SYMS = ['_','b','B','[',']','P','d','e','T','C','D','S','z','s','p','y']
T = {}
def st(name, rules, default=None):
    assert name not in T, name
    row = {}
    for s in SYMS:
        r = rules.get(s, default)
        if r is None: continue
        w, m, nx = r
        row[s] = (s if w is None else w, m, nx)
    T[name] = row
def scan(name, d, stops):
    st(name, stops, default=(None, d, name))
def hered(n, b=2):                       # canonical hereditary base-2 tree of n, as a level sequence
    out = []
    def rec(n, lvl):
        e = 0; terms = []
        while n:
            n, r = divmod(n, b); terms.append((e, r)); e += 1
        for e, r in reversed(terms):
            for _ in range(r): out.append(lvl); rec(e, lvl + 1)
    rec(n, 1); return out
cells = 'bb[]' + ''.join('P' + 'd' * k for k in hered(n))
for i, c in enumerate(cells):            # one init state per written cell
    last = i == len(cells) - 1
    st('I%d' % i if i else 'INIT', {'_': (c, 'L' if last else 'R', 'GSTEP_BUMP' if last else 'I%d' % (i + 1))})
# ---- Goodstein step: bump base, then subtract 1 ----
scan('GSTEP_BUMP', 'L', {'_': ('b', 'R', 'GO_CHOP')})
scan('GO_CHOP', 'R', {'_': (None, 'L', 'CHOP_START')})
st('CHOP_START', {'d': (None, 'L', 'CHOP_D1')})
st('CHOP_D1', {'P': ('_', 'R', 'CHOP_ERASE1'), 'd': (None, 'L', 'CHOP_FINDL')})
st('CHOP_ERASE1', {'d': ('_', 'L', 'STEP_DONE_CHECK')})
st('STEP_DONE_CHECK', {'_': (None, 'L', 'STEP_DONE_CHECK2')})
st('STEP_DONE_CHECK2', {']': ('HALT', 'L', 'HALT'), 'd': (None, 'L', 'GSTEP_BUMP')})
st('CHOP_FINDL', {'d': (None,'L','CHOP_FINDL'), 'P': ('T','L','CAND_FIND')})
st('CAND_FIND', {'d': (None,'L','CAND_FIND'), 'P': ('C','R','CMP_C')})
st('CMP_C', {'D': (None,'R','CMP_C'), 'd': ('D','R','CMP_TOL'), 'P': (None,'S','CMP_CEXH'), 'T': (None,'S','CMP_CEXH')})
scan('CMP_TOL', 'R', {'T': (None, 'R', 'CMP_L')})
st('CMP_L', {'D': (None,'R','CMP_L'), 'd': ('D','L','CMP_TOC'), '_': (None,'L','NOTPARENT')})
scan('CMP_TOC', 'L', {'C': (None, 'R', 'CMP_C')})
scan('CMP_CEXH', 'R', {'T': (None, 'R', 'CMP_LCHK')})
st('CMP_LCHK', {'D': (None,'R','CMP_LCHK'), 'd': (None,'R','PAR_END'), '_': (None,'L','NOTPARENT')})
scan('NOTPARENT', 'L', {'D': ('d','L','NOTPARENT'), 'C': ('P','L','CAND_FIND')})
scan('PAR_END', 'R', {'_': (None, 'L', 'ERASE_L')})
st('ERASE_L', {'d': ('_','L','ERASE_L'), 'D': ('_','L','ERASE_L'), 'T': ('_','L','MARK_END')})
st('MARK_END', {'d': ('z','L','UNMARK_S'), 'D': ('z','L','UNMARK_S')})
scan('UNMARK_S', 'L', {'D': ('d','L','UNMARK_S'), 'C': ('S','S','REP_START')})
# ---- replicate block [S .. z] b-1 times ----
scan('REP_START', 'L', {'[': (None, 'L', 'REP_FIRST')})
st('REP_FIRST', {'b': ('B', 'L', 'REP_SCAN')})
st('REP_SCAN', {'B': (None,'L','REP_SCAN'), 'b': ('B','R','GO_S'), '_': (None,'R','REP_DONE')})
scan('GO_S', 'R', {'S': (None, 'S', 'CP_SCAN')})
st('CP_SCAN', {'s': (None,'R','CP_SCAN'), 'p': (None,'R','CP_SCAN'), 'e': (None,'R','CP_SCAN'),
               'S': ('s','R','CARRY_P'), 'P': ('p','R','CARRY_P'), 'd': ('e','R','CARRY_D'), 'z': ('y','R','CARRY_DL')})
scan('CARRY_P', 'R', {'_': ('P', 'L', 'CP_RET')})
scan('CARRY_D', 'R', {'_': ('d', 'L', 'CP_RET')})
scan('CARRY_DL', 'R', {'_': ('d', 'L', 'CP_END')})
scan('CP_RET', 'L', {'s': (None,'R','CP_SCAN'), 'p': (None,'R','CP_SCAN'), 'e': (None,'R','CP_SCAN')})
scan('CP_END', 'L', {'y': ('z', 'L', 'CP_UNM')})
st('CP_UNM', {'e': ('d','L','CP_UNM'), 'p': ('P','L','CP_UNM'), 's': ('S','L','REP_RET')})
scan('REP_RET', 'L', {'[': (None, 'L', 'REP_SCAN')})
st('REP_DONE', {'B': ('b','R','REP_DONE'), '[': (None,'R','RD_S')})
scan('RD_S', 'R', {'S': ('P', 'R', 'RD_Z')})
scan('RD_Z', 'R', {'z': ('d', 'R', 'GO_CHOP')})

backs = {}
for name in list(T):
    for s, (w, m, nx) in T[name].items():
        if m == 'S':
            h = 'BACK_' + nx; backs[h] = nx; T[name][s] = (w, 'R', h)
for h, nx in backs.items():
    T[h] = {s: (s, 'L', nx) for s in SYMS}
T['STEP_DONE_CHECK2'][']'] = None          # undefined transition = halt
T['STEP_DONE_CHECK2'] = {k: v for k, v in T['STEP_DONE_CHECK2'].items() if v}
for name, row in T.items():
    for s, (w, m, nx) in row.items(): assert nx in T, (name, s, nx)
json.dump({'symbols': SYMS, 'start': 'INIT', 'seed': n, 'table': T}, open(sys.argv[2], 'w'), indent=0)
print('seed', n, 'tree', hered(n), '| states', len(T), 'symbols', len(SYMS), 'transitions', sum(len(r) for r in T.values()))
