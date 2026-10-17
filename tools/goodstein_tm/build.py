# Goodstein beeping Turing machine.  Builds the transition table; tm.json is the artifact.
# Tape: [BASE b..b] '[' [SEED over {N,u}] ']' [WORK: nodes 'P' d^depth ...].
# Per seed tree: b=2; repeat { b+=1; subtract-1 in base b } until WORK empty; BEEP; next seed.
import json, sys
SYMS = ['_','b','B','[',']','N','u','n','v','P','d','e','T','C','D','S','z','s','p','y']
T = {}
def st(name, rules, default=None):
    """rules: sym -> (write or None, move L/R/S, next).  default applies to unlisted symbols."""
    assert name not in T, name
    row = {}
    for s in SYMS:
        r = rules.get(s, default)
        if r is None: continue
        w, m, nx = r
        row[s] = (s if w is None else w, m, nx)
    T[name] = row
def scan(name, d, stops):            # move in direction d over unlisted symbols; stops handle the rest
    st(name, stops, default=(None, d, name))

# ---- init ----
st('INIT',  {'_': ('[', 'R', 'INIT2')})
st('INIT2', {'_': (']', 'L', 'INIT3')})
st('INIT3', {'[': (None, 'L', 'INIT4')})
st('INIT4', {'_': ('b', 'L', 'INIT5')})
st('INIT5', {'_': ('b', 'R', 'DEC0')})
# ---- decode seed into WORK ----
scan('DEC0', 'R', {']': (None, 'R', 'DEC_FIRST')})
st('DEC_FIRST',  {'_': ('P', 'R', 'DEC_FIRST2')})
st('DEC_FIRST2', {'_': ('d', 'L', 'DEC_NEXT')})
scan('DEC_NEXT', 'L', {'[': (None, 'R', 'DEC_FIND')})
st('DEC_FIND', {'n': (None,'R','DEC_FIND'), 'v': (None,'R','DEC_FIND'),
                'N': ('n','R','DEC_NODE'), 'u': ('v','R','DEC_U'), ']': (None,'L','DEC_UNMARK')})
scan('DEC_U', 'R', {'_': (None, 'L', 'DEC_U2')})
st('DEC_U2', {'d': (None, 'L', 'DEC_U3')})
st('DEC_U3', {'d': (None, 'R', 'DEC_U4'), 'P': (None, 'L', 'DEC_NEXT')})
st('DEC_U4', {'d': ('_', 'L', 'DEC_NEXT')})
scan('DEC_NODE', 'R', {'_': ('P', 'L', 'DEC_CFIND')})
st('DEC_CFIND', {'d': (None,'L','DEC_CFIND'), 'e': (None,'R','DEC_CPICK'), 'P': (None,'R','DEC_CPICK')})
st('DEC_CPICK', {'d': ('e','R','DEC_CCARRY'), 'P': (None,'R','DEC_CPLUS')})
scan('DEC_CCARRY', 'R', {'_': ('d', 'L', 'DEC_CRET')})
st('DEC_CRET', {'d': (None,'L','DEC_CRET'), 'P': (None,'L','DEC_CFIND')})
scan('DEC_CPLUS', 'R', {'_': ('d', 'L', 'DEC_UNP')})
st('DEC_UNP',  {'d': (None,'L','DEC_UNP'), 'P': (None,'L','DEC_UNP2')})
st('DEC_UNP2', {'e': ('d','L','DEC_UNP2'), 'P': (None,'L','DEC_NEXT')})
st('DEC_UNMARK', {'n': ('N','L','DEC_UNMARK'), 'v': ('u','L','DEC_UNMARK'), '[': (None,'L','GSTEP_BUMP')})
# ---- Goodstein step: bump base, then subtract 1 ----
scan('GSTEP_BUMP', 'L', {'_': ('b', 'R', 'GO_CHOP')})
scan('GO_CHOP', 'R', {'_': (None, 'L', 'CHOP_START')})
st('CHOP_START', {'d': (None, 'L', 'CHOP_D1')})
st('CHOP_D1', {'P': ('_', 'R', 'CHOP_ERASE1'), 'd': (None, 'L', 'CHOP_FINDL')})
st('CHOP_ERASE1', {'d': ('_', 'L', 'STEP_DONE_CHECK')})
st('STEP_DONE_CHECK', {'_': (None, 'L', 'STEP_DONE_CHECK2')})
st('STEP_DONE_CHECK2', {']': (None, 'L', 'BEEP'), 'd': (None, 'L', 'GSTEP_BUMP')})
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
# ---- beep and next seed ----
scan('BEEP', 'L', {'[': (None, 'L', 'NS_ERASE')})
st('NS_ERASE', {'b': ('_','L','NS_ERASE'), '_': (None,'R','NS_TOSEED')})
scan('NS_TOSEED', 'R', {']': (None, 'L', 'INC')})
st('INC', {'N': ('u','L','REBUILD'), 'u': ('N','L','INC'), '[': ('N','L','INC_NEWL')})
st('INC_NEWL', {'_': ('[', 'L', 'RB1')})
scan('REBUILD', 'L', {'[': (None, 'L', 'RB1')})
st('RB1', {'_': ('b', 'L', 'RB2')})
st('RB2', {'_': ('b', 'R', 'DEC0')})

# ---- compile 'S' (stay) moves into R + back-L helper states ----
backs = {}
for name in list(T):
    for s, (w, m, nx) in T[name].items():
        if m == 'S':
            h = 'BACK_' + nx
            if h not in backs:
                backs[h] = nx
            T[name][s] = (w, 'R', h)
for h, nx in backs.items():
    T[h] = {s: (s, 'L', nx) for s in SYMS}
# sanity: every referenced state exists
for name, row in T.items():
    for s, (w, m, nx) in row.items():
        assert nx in T, (name, s, nx)
json.dump({'symbols': SYMS, 'start': 'INIT', 'beep': 'BEEP', 'table': T}, open(sys.argv[1], 'w'), indent=0)
print('states', len(T), 'symbols', len(SYMS), 'transitions', sum(len(r) for r in T.values()))
