# Species Taxonomy 🧬

The conceptual spine for everything past v0.1. Records were trophy hunting. This is what conditional Collatz actually looks like.

## The map (fast version)

Define `T: ℕ⁺ → ℕ⁺` by

```
T(n) = (3n+1)/2   if n odd
T(n) = n/2        if n even
```

This is the **fast** Collatz / Syracuse function. It folds the obligatory `/2` after each `3n+1` into a single step. Mathematically equivalent to the slow `n → n/2 | 3n+1`, but cleaner for what follows.

(v0.1 used slow Collatz. Step counts differ. Not a contradiction - same dynamical system, different clock.)

## The parity vector

For each starting `n`, record at every step whether `T^i(n)` is odd (`1`) or even (`0`):

```
P(n) = (n mod 2, T(n) mod 2, T²(n) mod 2, ...)
```

Example, `n = 7`:

| step `i` | `T^i(7)` | parity |
|---|---|---|
| 0 | 7 | 1 |
| 1 | 11 | 1 |
| 2 | 17 | 1 |
| 3 | 26 | 0 |
| 4 | 13 | 1 |
| 5 | 20 | 0 |
| 6 | 10 | 0 |

So `P(7)` begins `(1,1,1,0,1,0,0, ...)`.

## The key theorem (Terras 1976 / Lagarias 1985)

> The first `k` bits of `P(n)` are determined by `n mod 2^k`.
> The map `Φ_k : ℤ/2^k → {0,1}^k` taking residue class to parity prefix is a **bijection**.

Two consequences worth pausing on:

1. **Every binary string is some species' parity prefix.** No constraint, no forbidden patterns. {0,1}^k is *covered* by residue classes mod `2^k`.
2. **At depth `k`, there are exactly `2^k` species.** Each species is a residue class mod `2^k`. Each species is uniquely identified by its parity prefix of length `k`.

## The phylogenetic tree

As `k` increases, each species splits in two:

```
depth k:        class r mod 2^k              parity prefix p of length k
                       │
                       ├─ class r mod 2^(k+1)        prefix p ++ [0]
                       │       (the half with 0 next)
                       │
                       └─ class (r + 2^k) mod 2^(k+1)  prefix p ++ [1]
                               (the half with 1 next)
```

It's a complete binary tree. Each level `k` has `2^k` nodes; each node is a residue class; each leaf at depth `k` is the parity prefix that uniquely identifies it.

This tree is the field guide's spine. Every cryptid is a node in this tree.

## Stopping time σ and graduation

For a starting value `n > 1`, define

```
σ(n) = min { i ≥ 1 : T^i(n) < n }   (or ∞ if no such i)
```

Standard companion theorem: σ is *constant on residue classes mod 2^σ*. So if `σ(r) = i ≤ k`, then **every** integer `m ≡ r (mod 2^k)` has `σ(m) = i`. The species is fully described by its smallest representative.

> **Species graduates at depth `k`** ⟺ for the smallest positive representative `r` (i.e. `r ∈ {1, …, 2^k - 1}`), we have `σ(r) ≤ k`.

The Collatz conjecture, restated:

> **Every species eventually graduates.**
> i.e. for every `r > 1`, `σ(r) < ∞`.
> Equivalently: as `k → ∞`, the fraction of graduated species → 1.

(For `r = 1`, σ is vacuous - 1 is the terminus, not a graduate. We treat it as a degenerate species and exclude it from counts when convenient.)

## What we hunt

- **Graduation curve** `ρ(k) = (graduated species at depth k) / (2^k - 1)`. Monotone increasing in `k`. *How fast* it approaches 1 is the open question with Tao-shaped tools applied to it.
- **Stubborn species** at our deepest probe `k = K_MAX`: residue classes `r mod 2^K_MAX` whose smallest representative hasn't dropped below itself within `K_MAX` fast-T steps. These are the cryptids — orbits that climb for a long time before yielding.
- (later) **Parity-prefix statistics**: are stubborn species' prefixes concentrated in some part of `{0,1}^k`? Lots of 1s? Specific patterns?

Each species is a node in the tree. Each cryptid is a node we haven't yet seen graduate. Field guide = annotated tree.

## A note on "conditional"

Every theorem above is conditional in the cryptid sense:

- *Conditional on parity prefix `p`*, the starting value lies in a known residue class.
- *Conditional on graduating at depth ≤ k*, σ is exactly determined by `n mod 2^k`.
- *Conditional on being a stubborn species at depth `k`*, the orbit climbs past its start for at least `k` steps - and we get to ask why.

No claim to prove anything global. We're describing what we see when we condition.
