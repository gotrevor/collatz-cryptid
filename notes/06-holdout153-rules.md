# Holdout 153 — The 16 Auto-Discovered Rules 🧬

All rules below were proved by Shawn's `Quick_Sim.py --recursive --verbose-prover`
running on the bbchallenge BB(3,3) holdout #153:

```
1RB0LB0RC_2LC2LA1RA_1RA1LC---
```

Raw extraction: `sim/153_all_rules.txt`. Run at `--max-loops 30000`. All 16 rules
were proved.

Notation: `XY^n` is `n` copies of the 2-symbol cell `XY` on the tape.
`<state` = head facing left at the indicated cell. `state>` = facing right.
Initial Config = pattern that must match for the rule to fire. Diff Config =
how each block's count changes when the rule fires (+ or - or "absent"=`0`).
Steps = number of underlying TM steps the rule advances.

## Family A — Sweep rules (12 of 16)

Constant time per application: **Steps = 6, Loops = 2**.
A state head sweeps **left** over a uniform block, decrementing the left block
by 2 and incrementing the right block by 2. Tail markers vary.

### Sub-family A.B02 — head `<B` over `(02)` cell, sweep `10 → 02`

| # | Tail markers (right of head) |
|---|---|
| 0  | `02^(b+1) 01¹ 11¹ 20¹` |
| 7  | `02^(?+1) 01¹ 11^(?+1) 12¹` |
| 10 | `02^(?+1) 01¹ 11^(?+1) 20¹` |
| 13 | `02^(?+1) 01¹ 20¹` |
| 14 | `02^(?+1) 01¹ 11¹ 12¹` |
| 15 | `02^(?+1) 01¹ 12¹` |

All six fire the same arithmetic: `10^(α+3) → 10^(α+1)`, `02^(β+1) → 02^(β+3)`,
markers consumed. They differ only in **which combination** of `{11, 20, 12}`
is present immediately right of the `02` block.

### Sub-family A.A20 — head `<A` over `(20)` cell, sweep `01 → 20`

| # | Tail markers |
|---|---|
| 3  | `20^(j+1) 12¹` |
| 4  | `20^(n+1) 11^(m+1) 12¹` |
| 9  | `20^(?+1) 11¹ 12¹` |
| 11 | `20^(?+1) 11^(?+1) 20¹` |

Same arithmetic: `01^(α+3) → 01^(α+1)`, `20^(β+1) → 20^(β+3)`, markers consumed.

### Sub-family A.C20 — head `<C` over `(20)` cell, sweep `01 → 20`

| # | Tail markers |
|---|---|
| 2  | *(none)* |

### Sub-family A.C12 — head `<C` over `(12)` cell, sweep `10 → 02`

| # | Tail markers |
|---|---|
| 6  | *(none)* |

## Family B — Expansion rules (4 of 16)

Linear time per application: **Steps = `8·d + 32`, Loops = 8**, where `d` is
the size of the inner-left `11` block. A state head moves **right** through
that block, growing it by 3 and shrinking the outer-left block by 2.

| # | Pattern |
|---|---|
| 1  | `10^(c+3) 11^(d+1) (11) B> 21¹ 11^(e+2) 20¹` → `10^-2 11^+3 (11) B> 11^-1` |
| 5  | `01^(q+3) 11^(r+1) (11) A> 11^(s+2) 12¹` → `01^-2 11^+3 (11) A> 11^-1` |
| 8  | `10^(?+3) 11^(?+1) (11) B> 21¹ 11^(?+2) 12¹` → `10^-2 11^+3 (11) B> 11^-1` |
| 12 | `01^(?+3) 11^(?+1) (11) A> 11^(?+2) 20¹` → `01^-2 11^+3 (11) A> 11^-1` |

Net effect of one expansion: outer-left `10` or `01` shrinks by 2, inner-left
`11` grows by 3, inner-right `11` shrinks by 1, tail markers consumed.

The matching state-symbol pair (`B>` or `A>`) is determined by which outer-left
block is present (`10` ↔ `B`, `01` ↔ `A`).

## Combinatorial picture

There are **2 head types** × **2 cell types** × **(several marker configurations)**:

| Outer block | Centre cell | Head | Marker variants | Family |
|---|---|---|---|---|
| `10` | `(02)` | `<B` | 6 | A.B02 |
| `10` | `(12)` | `<C` | 1 | A.C12 |
| `01` | `(20)` | `<A` | 4 | A.A20 |
| `01` | `(20)` | `<C` | 1 | A.C20 |
| `10` | `(11)` | `B>` | 2 | B.B11 |
| `01` | `(11)` | `A>` | 2 | B.A11 |

So 16 rules = 6 + 1 + 4 + 1 + 2 + 2.

## What this suggests (low confidence ~50%)

Holdout 153's behaviour likely admits a reduction to a discrete dynamical
system on **four counters** (corresponding to the four block types `10`, `01`,
`11`-inner, `02`/`20`-outer) plus a phase indicator (which of the six rule
sub-families applies next). Compare Bigfoot's `(a, b, c)` reduction: 3
counters, 6 mod-6 phases.

The Bigfoot-analogue would be something like `H153(α, β, γ, δ; phase) → ...`
with ~16 cases instead of 6. Writing that down explicitly — turning the 16
tape-pattern rules into a single arithmetic transition function — is the
**Phase 2** deliverable. Not done in this pass.

## Files

- `sim/153_all_rules.txt` — raw extraction (16 rules, 30k-loop run)
- `sim/153_verbose_full.txt` — earlier 500-loop run with full prover trace
