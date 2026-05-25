# Graduation Curve at K=20 📊

First serious species enumeration. K_MAX=20, 1,048,575 residue classes, fast T. Enumeration ran in 1.3s — plain Python, no optimization.

## The curve

```
   k    species    graduated    rate         1 - rate
   1          1            0    0.000000     1.00e+00
   2          3            1    0.333333     6.67e-01
   3          7            4    0.571429     4.29e-01
   4         15           11    0.733333     2.67e-01
   5         31           26    0.838710     1.61e-01
   6         63           54    0.857143     1.43e-01
   7        127          113    0.889764     1.10e-01
   8        255          235    0.921569     7.84e-02
   9        511          472    0.923679     7.63e-02     ← plateau
  10      1,023          958    0.936461     6.35e-02
  11      2,047        1,918    0.936981     6.30e-02     ← plateau
  12      4,095        3,868    0.944567     5.54e-02
  13      8,191        7,823    0.955073     4.49e-02
  14     16,383       15,648    0.955136     4.49e-02     ← plateau
  15     32,767       31,471    0.960448     3.96e-02
  16     65,535       63,420    0.967727     3.23e-02
  17    131,071      126,842    0.967735     3.23e-02     ← plateau
  18    262,143      254,647    0.971405     2.86e-02
  19    524,287      509,296    0.971407     2.86e-02     ← plateau
  20  1,048,575    1,021,246    0.973937     2.61e-02
```

## Three observations

### 1. Convergence is real but slow

`1 - ρ(k)` drops by roughly a factor of 2 every ~10 levels of `k`. From k=10 (6.35%) to k=20 (2.61%) is ~2.4× shrinkage over 10 levels — call it ~0.93x per +1 in `k`. Not the geometric blast you might hope for from a `(3/4)^k`-flavored heuristic. The conjecture is consistent with the data; the data is *not* loudly screaming "of course the conjecture holds." Interesting.

### 2. The plateaus 🪨

Every odd `k → k+1` transition shows a near-zero improvement in rate (8→9, 10→11, 13→14, 16→17, 18→19). Even `k → k+1` transitions move the needle. This is a *signature* — something structural about how species split.

Hypothesis: when a stubborn species at depth `k` splits into two children at depth `k+1`, the new step appended to the parity prefix is either `0` (even, halving) or `1` (odd, *3/2 multiplier). The halving child often graduates immediately (drops below start); the multiplying child rarely does. So odd → multiplying-only-on-the-decisive-step, no new graduations.

That's a guess. The actual mechanic is the next thing to nail down.

### 3. Stubborn species are heavily odd 🧬

Among the 27,329 stubborn species at k=20:

```
parity-prefix popcount:
  min  = 10
  mean = 14.23
  max  = 20         (all ones)
  uniform expectation = 10.0
```

Stubborn species' parity prefixes average **71% ones** vs 50% for a uniform random binary string. This is the *quantitative* version of the folk observation that "Collatz-resistant numbers do a lot of 3n+1 steps before they finally yield."

The max=20 entry: residue class `r ≡ 2^20 - 1 (mod 2^20)`, smallest representative `r = 1,048,575`. Its first 20 fast-T steps are all odd → orbit grows by `(3/2)^20 ≈ 3325×` before any drop possibility. A bona fide cryptid.

## Specimens of note

Smallest 10 stubborn species at k=20 (all odd, of course):

| r | parity prefix (LSB→MSB) | popcount |
|---|---|---|
| 1 | 01010101010101010101 | 10 |
| **27** | 11011101101011111011 | **16** |
| 31 | 01111011101101011111 | 15 |
| 47 | 10111101110110101111 | 14 |
| 63 | 11110111011000111111 | 14 |
| 71 | 01011110111011010111 | 13 |
| 91 | 10111001011110111011 | 14 |
| 103 | 10110111001011110111 | 13 |
| 111 | 11110011111101101111 | 15 |
| 155 | 11011011100101111011 | 14 |

`r = 1` is the degenerate "terminus" species — never drops below itself by definition. The rest are the real curiosities. `r = 27` makes the list with 16 ones — matches v0.1's altitude observation.

## What I want next (v0.3)

The plateau structure is the most interesting unknown. Two angles:

1. **Where do new graduations come from?** Per-step bookkeeping: at depth `k`, how many *new* species (not present at depth `k-1`) graduate? Is this concentrated on parity-prefix suffixes ending in `0`?
2. **The stubborn lineage tree.** A species stubborn at depth `k` has two children at depth `k+1`. Track: how often does both-stubborn happen vs one-graduates-one-stubborn? This tells us about the "fertility" of cryptid lineages.

Computational cost: both fit inside the existing enumeration with bookkeeping passes. No bigger `K_MAX` needed yet.
