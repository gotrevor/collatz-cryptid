# Regenerate the potential tree in lean/Collatz/HydraFoils/Cert218Data.lean from cert218.json
# (written by: node energy.js 4 3 '[1,2,3]' '[3,1,-1]' 59049 3 1 14 cert218.json).
# Usage: python3 gen218.py cert218.json lean/Collatz/HydraFoils/Cert218Data.lean
import json, sys
d = json.load(open(sys.argv[1])); phi = [int(v) for v in d['phi']]
Q, LE, NL, SPLIT = 59049, 32, 2048, 128
assert all(d['R']) and len(phi) == Q and max(phi) < 256
W = [3, 1, -1]
for u in range(3 * Q):  # independent re-check of the certificate
    s, r, b = u % Q, u % 3, 4 * (u // 3) + u % 3 + 1
    assert any(14 * W[r] + phi[(b + c) % Q] + 1 <= phi[s] for c in (0, 1)), u
leaves = []
for c in range(NL):
    T = 0
    for i in reversed(range(c * LE, min((c + 1) * LE, Q))): T = T * 256 + phi[i]
    leaves.append(T)
def build(off, stride, ind, out, top):
    if top and stride == SPLIT:
        out.append(' ' * ind + f"sub{off}"); return
    if stride == NL:
        v = leaves[off]
        out.append(' ' * ind + (f"(PTree.leaf 0x{v:x})" if v else "(PTree.leaf 0)")); return
    out.append(' ' * ind + "(PTree.node")
    build(off, 2 * stride, ind + 1, out, top)
    build(off + stride, 2 * stride, ind + 1, out, top)
    out[-1] += ")"
subs = []
for off in range(SPLIT):
    out = []; build(off, SPLIT, 2, out, False)
    subs.append(f"def sub{off} : PTree :=\n" + "\n".join(out))
out = []; build(0, 1, 2, out, True)
tree = ("\n\n".join(subs) + "\n\n/-- The potential, 32 entries of 8 bits per leaf (generated). -/\n"
        "def tree : PTree :=\n" + "\n".join(out))
p = sys.argv[2]; s = open(p).read()
a = s.index('def sub0 : PTree'); b = s.index('/-- The potential `φ` on')
open(p, 'w').write(s[:a] + tree + "\n\n" + s[b:])
