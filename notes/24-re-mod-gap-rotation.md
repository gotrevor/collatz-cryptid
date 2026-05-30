# 24 — R(e) mod gap: equidistribution = noise + rotation symmetry 🪷

**Date**: 2026-05-28 (next-session continuation of notes/23). **Mode**: pure exploration.
Scripts: `~/personal/tools/sandbox/re_mod_gap.py`, `re_mod_gap_v2.py`.

Targets **open question (D)** from the notes/23 wrap (the difficulty-locus-correct one):
does the Lagarias cycle remainder `R(e)` equidistribute mod `gap = 2^L − 3^n` as `e`
ranges over compositions of `L` into `n` positive parts? `gap` is "2 ≠ 3" made a number;
`R(e) ≡ 0 (mod gap)` are exactly the `d=1` Collatz cycle CANDIDATES
(`x·gap = d·R(e)`, so `x = R(e)/gap`).

## Result

**R(e) equidistributes mod gap — pure "2≠3 noise" — modulo the ℤ/n rotation symmetry of
cycles, which is provable.** The raw `#{R≡0}` overcounts the uniform expectation
`ncomp/|gap|`, but every excess is a full rotation orbit. Quotient by rotation and the
orbit count drops to `~ncomp/(n·|gap|)` (≈ the Eliahou heuristic). No structure beyond
the obvious symmetry. Verified rotation-closed in all 7 tested `(n,L)`.

## Keeper — Lemma: rotation-invariance of the cycle divisibility

Let `e' = (e_2,…,e_n,e_1)` be the one-step rotation of `e`. Then

  `2^{e_1} · R(e') = 3·R(e) + d·gap`     ⟹     `2^{e_1}·R(e') ≡ 3·R(e)  (mod gap)`.

`gap = 2^L − 3^n` is **odd** (even − odd), so `gcd(2^{e_1}, gap) = 1`, hence

  **`gap | R(e)  ⟺  gap | R(e')`.**

So `d=1` cycle candidates occur in full ℤ/n rotation orbits.

**Proof.** With `d=1`: the next cycle element is `x' = (3x+1)/2^{e_1}`, i.e.
`2^{e_1} x' = 3x + 1`. Multiply `x'·gap = R(e')` by `2^{e_1}`:
`2^{e_1}R(e') = (3x+1)·gap = 3(x·gap) + gap = 3R(e) + gap`. General `d`: `+d·gap`. ∎

This is the algebraic statement that "a cycle doesn't care which element you start from",
read off `R` mod `gap`. Lean-formalizable (small; sits next to `Lagarias.lean`).

## Validation (unexpected, strong)

The only two non-noise orbits found are genuine cycles **of the negative integers**:

| orbit rep `e` | `n` | `L` | `gap` | `x = R/gap` |
|---|---|---|---|---|
| `(1,2)×5` | 10 | 15 | −26281 | **−5** |
| `(1,1,1,2,1,1,4)` | 7 | 11 | −139 | **−17** |

`{−1, −5, −17}` are the **three known negative 3x+1 cycles** (`−1` lives in the skipped
`|gap|=1` trivial case). The probe rediscovered `−5` and `−17` from scratch as the *only*
structure in range, and found **zero positive-cycle candidates**. Correctness check on the
whole `R(e)/gap` machinery passed. `(1,2)×5` is the non-primitive 5-fold copy of the
primitive `(1,2)` (n=2, L=3) `−5` cycle.

## Verdict on "2 ≠ 3" (difficulty-locus honest)

Inside the **Diophantine face**, the Collatz cycle obstruction is pure
multiplicative-independence pseudorandomness modulo ℤ/n rotation — exactly the Eliahou
prediction, now machine-confirmed and with the symmetry made explicit. The "deep
relationship" sought here is the *absence* of one: noise + the rotation lemma, nothing
more. Same shape as the notes/23 Mahler keeper (clean negative, lemma fished out). No
overclaim: the rotation lemma is elementary; its value is as a precise, formalizable
statement, not a new phenomenon.

## Lean formalization ✅ (2026-05-28, same session)

`Collatz/Erdos/Cycle.lean` (builds clean, 0 sorries, in `Erdos.lean` aggregator):

- `cycleR : List ℕ → ℕ` — the cycle remainder, recursive form
  `R(a::rest) = 3^|rest| + 2^a · R(rest)`, `R([]) = 0`.
- `cycleR_append_single` — `R(l ++ [a]) = 3·R(l) + 2^{Σl}` (induction).
- **`cycleR_rotate`** (ℕ, exact, subtraction-free): `2^a·R(e') + 3^n = 3·R(e) + 2^L`.
- **`cycleR_rotate_int`** (ℤ): `2^a·R(e') = 3·R(e) + gap`, `gap = 2^L − 3^n`.
- `cycleGap_odd` (needs `Σe ≥ 1`) + `not_three_dvd_cycleGap` — the two coprimalities.
- **`cycleGap_dvd_cycleR_iff`** (the keeper): `gap ∣ R(e) ⟺ gap ∣ R(e')`.
- Sanity `example`s pin the `−5` and `−17` negative cycles (`decide`).

Proof spine: ℕ identity by `cycleR_append_single` + `pow_succ`/`pow_add` + `ring`;
cast to ℤ via `exact_mod_cast` + `push_cast` + `linarith`; iff via
`IsCoprime.dvd_of_dvd_mul_left` with `gap` coprime to 2 (odd, `Int.odd_iff` + `omega`)
and to 3 (`Prime.dvd_of_dvd_pow`). Names verified against mathlib master before use.

## Fork 2 (open question C): the "1-cycle d's" 🪷 (2026-05-28)

`C = { d odd > 0 : x=1 lies in a cycle of the accelerated 3x+d map }`.
Enumerated by direct iteration from `x=1` (`~/personal/tools/sandbox/re_one_cycle_d.py`),
odd `d ∈ [1, 4000]`: **|C| = 178**, density ≥ 0.089 (lower bound — step-capped, large-`n`
cycles missed; some members have `n` up to 354).

**Structure (the keeper):** split C by cycle length `n`:
- **n=1 family** = exactly `{2^L − 3}` = `{1,5,13,29,61,125,253,509,1021,2045}` (the
  direct fixed points `1 → (3+d)/2^L → 1`). Confirmed: all are `2^L − 3`.
- **n≥2 remainder** (168 members: 11, 17, 41, 43, 55, 59, 77, 79, 91, 95, 97, …).

**Every member of C is coprime to 3** — `d mod 6` histogram on the n≥2 set is
`{1: 83, 5: 85}` and **zero** elsewhere; the n=1 family `2^L−3` is also `3∤`.
This is **forced, not empirical**: the x=1 cycle equation is `d · R(e) = gap`, and
`3 ∤ gap` (proved: `not_three_dvd_cycleGap`), so `3 ∤ d`. Fork 2 ⟸ fork 1's coprimality.

**Lean'd**: `three_not_dvd_one_cycle_d` in `Cycle.lean` (from `d·R(e)=gap` ⟹ `3∤d`),
with the `d=11` witness (`e=(1,5)`, `R=5`, `gap=55=11·5`) pinned by `decide`.

**No further clean structure found** (difficulty-locus honest): `d mod 8` is spread
`{1,3,5,7}`, consecutive ratios → 1, and naive closure maps (`4d±?`, `2d+1`) give only
scattered hits, no closure. So `C ⊆ {d : 3∤d}` (proven, proper subset); beyond the mod-3
constraint and the `2^L−3` spine, C looks like a generic sparse set.

**Novelty caveat**: the 3x+d generalized map and its rational cycles are well-studied
(Lagarias 1990, "rational cycles for 3x+1"). The mod-3 constraint is elementary — likely
folklore in that literature. Honest contribution = the clean Lean tie to the gap lemma,
not a new theorem. Did not find a novel phenomenon in C; the spine + mod-3 is the content.
