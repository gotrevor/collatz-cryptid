# 23 — Mahler dead-end + the m=5 S-unit Universal Frontier 🪷

**Date**: 2026-05-28. **Mode**: pure exploration (no Lean), per Trevor's directive "find relationships between unknown conjectures or create our own; anything well-known is an axiom." Sandbox scripts in `~/personal/tools/sandbox/collatz_*.py`, `sunit_family.py`, `diophantine_cycles.py`.

This note records two keepers from a session that chased the "Lehmer/Mahler ⟶ Collatz cycle" wildcard. The Mahler bridge **failed** (clean negative, with a theorem fished out of the wreckage). The S-unit reframing **succeeded** as a relationship-between-conjectures and a novel meta-conjecture.

## Keeper 1 — Theorem: Lagarias cycle polynomials have constant Mahler measure

**Setup.** A compressed-Collatz cycle of length `n` with exponent vector `e = (e_1,...,e_n)`, `L = Σ e_i`, `S_k = e_1+...+e_k`, has Lagarias remainder
`R(e) = Σ_{j=1}^n 3^{n-j} · 2^{S_{j-1}}`, and the cycle equation `x·(2^L − 3^n) = d·R(e)` (for `3x+d`). Define the **cycle polynomial**
`P_{n,e}(z) = Σ_{j=1}^n 3^{n-j} · z^{S_{j-1}}` so that `R(e) = P_{n,e}(2)`.

**Theorem.** For *every* composition `e` of `L` into `n` positive parts, the Mahler measure is
`M(P_{n,e}) = 3^{n-1}`. (Constant — independent of `e`.)

**Proof.** `P_{n,e}` is monic (leading coeff `3^0 = 1` at degree `S_{n-1}`), constant term `3^{n-1}`, all coefficients positive powers of 3 in geometrically-decreasing pattern. If `|z| < 1`:
`|Σ_{j≥2} 3^{n-j} z^{S_{j-1}}| ≤ Σ_{j≥2} 3^{n-j} = (3^{n-1} − 1)/2 < 3^{n-1}`,
so `P(z) ≠ 0`. Hence **all roots have `|z| ≥ 1`** (strictly `> 1`, with slack). For a monic polynomial with all roots outside the closed unit disc, `M = ∏ max(1,|root|) = ∏|root| = |constant term| = 3^{n-1}`. ∎

Equivalently: the family of Lagarias cycle polynomials is a **uniformly reciprocal-Schur class** (their reciprocals `z^d P(1/z)` are all Schur-stable, all roots in the closed unit disc). Verified numerically for n=2..8 and n=12,17 across thousands of `e`: `min = mean = median = max = 3^{n-1}` every time. Script: `collatz_cycle_mahler.py`.

## Keeper 1b — Why Mahler can't see cycles (the structural reason)

Cycle existence is `gap | d·R(e)` where `gap = 2^L − 3^n` — a **residue-class** condition. Mahler measure is a **size** invariant (product of root moduli outside unit disc). These are different categories: Mahler smooths away the residue information. A near-cyclotomic `P` (M≈1) would force `R = P(2)` *small*, but smallness doesn't help divisibility — you need `R` in a specific class mod `gap`. So no Mahler/Lehmer-style invariant can bridge to the cycle obstruction. This kills the wildcard cleanly and tells us *which kind* of math the obstruction lives in (Diophantine / S-unit, not algebraic-spectral).

Sub-findings discarded en route (recorded so we don't re-chase):
- **Encoding A** (raw parity {0,1}-polynomial): apparent Mahler deficit (z ≈ −1.18 vs random) is **entirely explained** by the trivial "no two consecutive 1s" constraint (odd-Collatz: 3·odd+1 is even). Constrained-shuffle control → z ≈ +0.12. No arithmetic signal. (`collatz_mahler_v3.py`)
- **Encoding A'** (Lagarias exponent polynomial `Σ e_i z^i`): small residual deficit z ≈ −0.28, dominated by short-orbit artifacts (orbits ending `5→1` give leading coeff 4). Not robust. (`collatz_mahler_v4.py`)
- **σ = min root modulus**: cycle witnesses *looked* high-σ (median √3 vs 1.43) but this **confounded by the diagonal** (n,L) where gap = d; sporadic witnesses (gap ≫ d) show only weak σ-anomaly. (`collatz_root_spectrum.py`, `collatz_sporadic.py`)
- **Zero sporadic d=1 candidates** found up to (n=10, L=20): consistent with no nontrivial 3x+1 cycle below ~10⁹.

## Keeper 2 — The m=5 S-unit Universal Frontier (novel meta-conjecture)

**The relationship.** Both Erdős and Collatz-cycles are equations in the {2,3}-S-unit family `Σ c_i 2^{a_i} 3^{b_i} = 0` (fixed small `c_i`):
- **Erdős k** (`2^N = 3^{a_1}+...+3^{a_k}`, distinct powers) → **(k+1)-term** equation.
- **Collatz n-cycle** (x=1: `2^L = 3^n + Σ_{j=1}^n 3^{n-j}2^{S_{j-1}}`) → **(n+2)-term** equation.

So they coincide at term count when **k = n+1**: Erdős k=4 and Collatz 3-cycle are *both 5-term* equations (same species; not the same equation — Erdős is pure powers of 3, Collatz mixed). Verified term-by-term in `sunit_family.py`.

**Effectivity ladder** (term count governs difficulty):

| terms | example | reachable by |
|---|---|---|
| 3 | `a·2^x + b·3^y = 1` | Baker (effective) ✅ |
| 4 | + 1 S-unit | Baker + p-adic valuation tricks |
| **5** | Erdős k=4 / Collatz 3-cycle | subspace thm (ineffective) **or** abc |

**Master conjecture** (child of abc, parent of both): *Effective {2,3}-S-unit* — for each `m` there's an effectively computable `B(m)` bounding all non-degenerate solutions of any `m`-term equation. Implied by abc; implies effective-Erdős (all k) AND effective-no-Collatz-cycle (all n).

**Novel meta-conjecture — "m=5 Universal Frontier":** m=5 is the *simultaneous* effectivity threshold for the {2,3}-S-unit family. A single effective bound for the generic 5-term equation would resolve Erdős k=4, the Collatz 3-cycle question, and the analogous 5-term Pillai instances **all at once** — they share one wall, they are not independently hard. (Falsifiable: find a 5-term {2,3} instance that's effectively solved by methods that *don't* generalize, or a sub-5-term instance that's genuinely open.)

**Erdős computation** (`sunit_family.py`): up to N=5000 the only powers of 2 that are sums of distinct powers of 3 are **N ∈ {0, 2, 8}** (k = 1, 2, 4; no k=3). Min nonzero ternary-digit count grows steadily (206 by N=500 → 1850 by N=4500): Erdős "digits → ∞" visible in-range. Matches the `Collatz/Erdos/` Lean catalogue (notes/22): k=1,2,3 proved, k=4 open.

## Honesty corrections logged
- First draft of the correspondence table attributed "Collatz 1-cycle PROVED (Steiner '77), 2-cycle (Simons '05)." **Misattribution**: Steiner / Simons-de Weger classify cycles by *number of circuits*, NOT by odd-step-count `n`. Those results do not cleanly map onto the n-by-odd-steps axis. The defensible claim is the term-count/effectivity parallel + abc umbrella, not a tidy proved/open Collatz column.
- The original pitch said "Erdős k=4 ⟺ Collatz 3-cycle." After the off-by-one scare, the careful term count **confirms** it (both 5-term). Pitch vindicated.

## Survey result + RETRACTION of the strong frontier claim

Survey (`sunit_frontier.py`, `sunit_independent.py`) confirmed the term-count ladder across a genuinely independent family (`r` powers of 2 = `s` powers of 3): 3-term small-finite, 4-term finite-bounded, 5-term sporadic ({28, 82, 84, 324} for (3,2)). Looked supportive.

**⚠️ But Trevor's critique (2026-05-28) breaks the strong "resolve 5-term ⟹ resolve all" claim. He's right. Two corrections:**

1. **Difficulty is asymptotic, not at the smallest open case.** A large Erdős counterexample `2^n` (n>8) has `~0.63n` ternary digits → term count `k ~ 0.63n`, *growing with n*. A nontrivial Collatz cycle has n in the billions (Eliahou). So the hard regime is large-parameter (the exceptional/outlier set) — the same density-1-easy / measure-0-hard structure as Tao 2019. Resolving m=5 strips only the smallest sporadic shell.

2. **m=5 isn't even special for provability.** Finiteness at *fixed* k (incl. k=4) is already a theorem (subspace theorem, Evertse/Schlickewei–Schmidt) — just *ineffective*. The ineffectivity wall is m=4 and is the *same wall at every m ≥ 4*. No distinguished 5. The 4-vs-5 gap was only about which cases *elementary* tricks clear — a patchwork.

**What survives**: (a) these are {2,3}-S-unit / linear-forms-in-logs instances (known: Lagarias, Eliahou); (b) shared abc umbrella for *effective* resolution (known, not novel). The S-unit tie is real but textbook, NOT a novel relationship.

**Lean**: `Collatz/Erdos/SUnit.lean` (builds clean, in aggregator). Keeps the family defs, the proved ≤3-term reuse, the *5-term coincidence* (relabeled from "frontier", shallow), and `AsymptoticContent`/`asymptotic_is_the_master` encoding the honest target (uniform-in-k = the load-bearing statement). Module docstring records the full critique.

## Outlier-structure test: do log₂3 convergents govern BOTH exceptional sets? → NO (2026-05-28)

Tested whether continued-fraction convergents of log₂3 govern both Collatz cycle locations and Erdős exceptions (`log23_convergents.py`). **Verdict: convergents govern Collatz (Eliahou, confirmed) but NOT Erdős. The overlap is coincidence.**

- **Collatz ✓**: min `|2^L−3^n|/3^n` clusters at convergent `(L,n)` pairs (2/1, 8/5, 19/12...). n=5 gap 0.053, n=12 gap 0.013 — local minima exactly at convergent denominators. Eliahou's mechanism, confirmed.
- **Erdős ✗**: exceptions {0,2,8}; from-above convergent numerators {2,8,65,485,...}. Yes {2,8} ⊂ numerators — BUT **decisive counterexample n=65**: a near-perfect from-above numerator (`{65·log₃2}=0.0104`, leading digit 1) with **14 interior 2's** — not remotely an exception. So approximation quality does NOT predict exception status.
- **Why it's coincidence**: an Erdős exception only needs leading digit ≤1, i.e. `{n·log₃2} < log₃2 ≈ 0.63` — true for **63% of all n**, NOT convergent-level smallness. The no-2 condition is a property of the *entire* base-3 digit string, governed by the base-3 doubling dynamics (`DoublingCA.lean`), which the Diophantine approximation does not control. Overlap {2,8}: expected ~1 by chance, observed 2 — mild, consistent with both sets being small-number-heavy.

**Structural divergence (the real finding)**: Collatz difficulty lives at the **Diophantine-approximation** level (gap = convergent-governed; Baker / irrationality measure of log₂3). Erdős difficulty lives at the **full-digit-string / automata** level (base-3 doubling CA; Cobham / multiplicative-independence territory). Both are "2-vs-3" problems but the relevant structures are genuinely different — naive bridges between them are trivial (shared irrationality) or coincidental (m=5, convergent overlap).

## Session meta-conclusion
Across Mahler, m=5, and convergent-governance, **every proposed Collatz↔Erdős bridge collapsed to trivial-or-coincidental.** That is itself the result: the surface "both about powers of 2 and 3" does NOT yield deep coupling. If Erdős has a natural structural home it's **automatic sequences / Cobham** (base-3 doubling CA), a different continent from Collatz's Diophantine-approximation home. Candidate genuinely-novel next pivot: formalize the Erdős↔Cobham link (multiplicative independence of 2,3 ⟹ digit-string rigidity), which `DoublingCA.lean` already gestures at.
