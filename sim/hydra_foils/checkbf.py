# Re-check a Bigfoot lifted certificate (output of energy.js ... M 3 d m out.json).
# usage: python3 checkbf.py out.json M d m   -> checks all u < 24*M, prints packed hex (5 bits)
import json, sys
f, Q, d, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
phi = [int(x) for x in json.load(open(f))['phi']]
H = [0,-2,5,7,0,9,10,6,0,14,13,17,0,17,26,22,0,30,27,25,0,31,26,38]
W = [0,1,0,0,0,0,0,1,0,0,1,0,0,1,-1,0,0,-1,0,1,0,0,1,-1]
for u in range(24 * Q):
    img = 32 * (u // 24) + H[u % 24]
    assert any(m * W[u % 24] + phi[(img + c) % Q] + 1 <= phi[u % Q] for c in range(d + 1)), u
v = 0
for i, x in enumerate(phi):
    v |= x << (5 * i)
print("ok max phi", max(phi))
print(hex(v))
