# V6 k_pos: swing attempt 🪓

Date: 2026-05-26.

## Goal

Prove `∀ n, ∀ s, V6.orbit n = some s → 1 ≤ s.k`.

Equivalently (via the bijection φ derived in `bigfoot_compare_v6_shawn.py`):
prove Shawn's `a ≥ 1` invariant on the (a,b,c) orbit. Same theorem in two
coordinate systems.

## Status: partial — cascade structure mapped, not closed

This file documents the swing's findings. The cascade DOES seem to bottom out
at impossible preimages (good sign), but completing it requires a
substantial Lean development. We did not close it in this session.

## Bijection refresher

```
φ(a_s, b_s, c_s) = (a_s, 2·b_s − 1, 2·c_s + 1, P1)
φ⁻¹(k, a_v, b_v, P1) = (k, (a_v+1)/2, (b_v−1)/2)   when a_v, b_v both odd
```

Empirically: first 10 Shawn states all appear in V6's orbit at V steps
0, 2, 4, 6, 9, 14, 19, 26, 36, 50. V6 has ADDITIONAL invertible states
between consecutive Shawn states (V6 super-cycle is finer than Shawn Dyn).

## The k_pos question in V6 coords

V6's k changes at boundary rules:
- **Δk = +1**: Q-W (a=7), Q-kpp (a=1).
- **Δk = −1**: B-coll (a=9), D-W (a=3).
- **Δk = 0**: S, B, W, Q-same, P2→P1.

Initial k = 2. For k ≥ 1 always, we need:
  `#(B-coll + D-W firings) ≤ #(Q-W + Q-kpp firings) + 1`
on every orbit prefix.

## Pairing analysis

**B-coll always immediately recovers** because its output is `(k−1, 1, b+12, P1)`,
and `a=1` forces Q-kpp next, giving `(k, b+12, 3, P2)`. Net Δk = 0 for the pair
(B-coll, Q-kpp). So B-coll is "safe" as long as input k ≥ 2.

**D-W is the trouble case.** Output `(k−1, b+7, 0, P1)` has `a = b+7 ≥ 12`
(since D-W input b ≥ 5 — see "reachability constraints" below). Then S/B
alternation begins, and the next boundary rule is determined by `(b+7) mod 12`.

D-W's k decrement is NOT immediately recovered. It's recovered eventually
when the trajectory hits a=1 (Q-kpp) or a=7 (Q-W). But the trajectory might
pass through another a=3 (D-W) or a=9 (B-coll) before recovery — which would
cause a second decrement.

## D-W input b analysis

Where can D-W fire? It fires when state is `(k, 3, b, P1)`. Preimages of
`(P1, a=3)`:

- **From S** (input a=6): preimage `(k, 6, b−5, P1)`. Output b = `b_S_in + 5`,
  so D-W input b ≥ 5.
- **From P2→P1** (input a_p2=7): preimage `(k, 7, b−4, P2)`. Output b =
  `b_p2 + 4`. P2 has b ≥ 2 (Q-same gives b=2, Q-kpp gives b ≥ 5), so D-W
  input b ≥ 6.

Combined: **D-W input b ≥ 5**.

### Reachable D-W input b values

By recursive preimage chase (see body), reachable D-W input b values seem
to be tightly constrained. I verified by hand:

| D-W input b | Reachable? | Post-D-W trajectory | Risk |
|---|---|---|---|
| 5 | **NO** — preimage chain blocks at (k, 2, 2) which forces b ≥ 11 | would lead to a=9 → B-coll, second decrement | n/a |
| 6 | **NO** — preimage chain blocks | would lead to Q-kpp, safe | n/a |
| 7 | **YES** — V@186 in actual orbit, k_in=4 | a=14 → ... long S/B chain → eventually Q-same (k unchanged) → P2→P1 → ... | k stays decremented but recovers far later |
| 8 | **NO** — blocks | (n/a) | n/a |
| 9 | NOT VERIFIED (likely no) | unknown | unknown |
| 11 | **NO** — blocks | would lead to second D-W, double decrement | n/a |
| 12 | **NO** — blocks | would be safe (Q-W recovery) | n/a |
| 13 | **NO** — blocks | unknown | unknown |

The reachable D-W input b values are SPARSE. Many "dangerous" b values
(like b=5 that would lead to immediate B-coll) are blocked by unreachable
preimage chains.

The structural reason: P2 states have constrained b values (only 2 from
Q-same and ≥5 from Q-kpp). So P2→P1 output b ∈ {6, 9, 10, 11, ...}. Most
"problem" values of D-W input b can only come from impossible preimage
chains.

## What's blocked vs. open

### Blocked (provable in Lean)

1. **(P1, a=2, b<11) unreachable**: only B produces (P1, a=2), and B's output b = input_B_b + 11 ≥ 11. ✓
2. **(P1, a=5, b<2) unreachable**: similar analysis. Cascades from impossible preimages.
3. **(P1, a=3, b≤4) unreachable**: from S, b_S_in + 5 ≥ 5; from P2→P1, b_p2 + 4 ≥ 6.
4. **D-W input b ∈ {5, 6, 8, 11, 12, 13} unreachable**: documented above by case analysis.

These together rule out **most** of the "fast double-decrement" chains.

### Open (the genuine math content)

- **Is D-W input b ∈ {7, 9, 19, ...} reachable, and does the post-D-W trajectory always recover before another decrement?**
- More precisely: is there a clean structural classification of reachable D-W input b values, AND for each, a bound on the number of "k-stable" steps before recovery?

If yes: V6 k_pos is provable. The proof is a multi-clause inductive invariant.

If no (but empirically holds for 1B cycles): we'd need a non-elementary argument (maybe a density/asymptotic argument).

## What the swing produced

1. **Documented bijection** (above + `bigfoot_compare_v6_shawn.py`, `bigfoot_bijection_check.py`).
2. **Sparseness of D-W reachable b** (manual analysis): rules out many "fast" double-decrement chains.
3. **Strategic decision needed**: continue this case analysis to closure (estimated days of Lean work for the full cascade), or pivot to TM-correspondence path A.

## Notes for next session

- The `b ≥ 11 at a=2` constraint is a strong structural fact. Worth formalizing as a Lean lemma even if k_pos isn't closed.
- The P2 b-value constraint (`b=2 or b≥5`) is the root cause of many blocked preimage chains. Also worth formalizing.
- These structural lemmas combined would give an enriched `Inv` structure with maybe 8-12 clauses. Preservation of each is mechanical but tedious.
- The OPEN content is genuinely subtle: it's the asymptotic balance between increment and decrement rule firings.

## Files

| File | Role |
|---|---|
| `tools/sandbox/bigfoot_shawn_dyn.py` | Shawn's (a, b, c) Dyn rule simulator |
| `tools/sandbox/bigfoot_compare_v6_shawn.py` | Side-by-side TM simulation tabulating both boundary types |
| `tools/sandbox/bigfoot_bijection_check.py` | Verifies φ as a bijection at every Shawn-vs-V6 boundary |
| `notes/18-v6-k-pos-attempt.md` | This file |
