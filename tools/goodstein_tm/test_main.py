import sys; sys.setrecursionlimit(100000)
from check import *
def bump(n, b, c):                          # rewrite n from hereditary base b to base c (integers only)
    r, e = 0, 0
    while n:
        n, d = divmod(n, b)
        if d: r += d * c ** bump(e, b, c)
        e += 1
    return r
events = []; S = {'seed': None}
def on(ev, tape, n):
    b, seed, depths, work = regions(tape)
    if ev == 'BEEP':
        S['base'] += 1; S['k'] += 1; S['ref'] = sub1(S['ref'], S['base'])
        if S['g'] is not None: S['g'] = bump(S['g'], S['base'] - 1, S['base']) - 1
        assert depths == [] and S['ref'] == [] and (S['g'] is None or S['g'] == 0), S
        events.append(('BEEP after seed', seed, 'goodstein steps', S['k'], 'tm steps', n)); S['seed'] = None; return
    if S['seed'] != seed:
        assert depths == decode_seed(seed) and b == 2, (seed, depths, b)
        canon = depths == hered(value(depths, 2), 2)
        S.update(seed=seed, ref=depths, base=2, k=0, g=value(depths, 2) if canon else None)
        events.append(('SEED', seed, depths, 'canonical n=%s' % S['g'] if canon else 'non-canonical'))
        return
    S['base'] += 1; S['k'] += 1
    S['ref'] = sub1(S['ref'], S['base'])
    assert depths == S['ref'], ('hydra mismatch', seed, S['k'])
    assert b == S['base'], ('base', b, S['base'])
    if S['g'] is not None:
        S['g'] = bump(S['g'], S['base'] - 1, S['base']) - 1          # independent big-int Goodstein
        assert value(depths, S['base']) == S['g'], ('goodstein mismatch', seed, S['k'])
    S['checked'] = S.get('checked', 0) + 1
run(int(sys.argv[1]), on_event=on)
for e in events: print(e)
print('steps checked:', S.get('checked'), '| current seed', S['seed'], 'goodstein step', S.get('k'), 'base', S.get('base'), 'value', S.get('g'))
