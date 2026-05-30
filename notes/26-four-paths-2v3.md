# 26 — Four paths to 2↔3 relationships (creative sweep) 🪷

**Date**: 2026-05-28 (same session as notes/24,25). Trevor: "assuming you're a
creative genius, what paths are worth pursuing... do them all, one by one."
Ran the concrete first step of each. Scoreboard: **2 wins, 1 bankable hub, 1 honest null.**

Guiding frame: don't bridge *between* the three faces (magnitude / digit / dynamics)
— those collapse (category error). Aim at the **interface objects** that legitimately
project onto more than one face.

## Path 1 — Carries are the magnitude↔digit interface ✅ WIN

A base-3 digit `2` in `2^n` is *produced by the carry rule* of the doubling CA.
A carry fires when the local sum reaches the base (`2d+c≥3`, a magnitude threshold)
yet is a digit-level event — so it sits ON the seam.

- **Numerics** (`~/personal/tools/sandbox/path1_carry.py`, n≤500): carry density →
  **0.498 ≈ ½**, digit-2 density → **0.331 ≈ ⅓** — exactly the carry-rule heuristic.
  Even-n near-exceptions (n=2,8: 0 twos; n=4,6,24: 1 two) = "carry never makes a 2".
- **Lean** (`Carry.lean`, 0 sorries): `doubleDigit_fst_eq_two` (output=2 ⟺ carry state
  `(1,0)`/`(2,1)`), `doubleDigit_carry_eq_one` (carry ⟺ `2d+c≥3`), and
  `ErdosAsCarryPositivity` (Erdős = the doubling carry field is never 2-sparse).
- **Verdict**: the interface object is real and now formal. The carry process is a
  single object both faces project from. Best candidate for a genuinely novel framing.
- **UPGRADE (next session, 2026-05-28): `ErdosAsCarryPositivity` is now a *theorem*, not a
  reframing.** `digits_three_two_pow : Nat.digits 3 (2^n) = iterCA n` (in `DoublingCA.lean`)
  proves the doubling-CA list **is** the canonical base-3 rep of `2^n`, via mathlib's
  `Nat.digits_ofDigits` + two CA invariants: `doubleAux_lt_three` (digits stay `<3`) and
  `doubleAux_getLast?_ne` (no leading zero — the carry threads nonzero-ness up to the high
  digit). Then `erdos_iff_carryPositivity : ErdosConjecture ↔ ErdosAsCarryPositivity` is a
  genuine logical equivalence, `#print axioms` clean (propext/choice/quot only — **no project
  axiom, no sorry**). `ErdosAsCarryPositivity` was redefined to the real `∀ n>8, 2 ∈ iterCA n`
  (the old def was a vacuous placeholder satisfiable by `d=1,c=0`). The witnessing `2` ties
  back to the carry rule via `two_in_iterCA_is_carry_made`.
- **SWING #5 (same session): the carry-process *coupling object* (`CarryProcess.lean`,
  0 sorries, axiom-clean — propext+Quot.sound only).** Defines `carryCount L c` and proves
  **Kummer conservation `s(2L) + 2·C(L) = 2·s(L)`** (`digitSum_doubleBase3`), so the carry
  count IS the digit-sum deficit `(2s−s')/2` (`carryCount_eq_digitSum_deficit`), plus the
  per-step `2^n` digit-sum recurrence (`digitSum_iterCA_succ`). This is the single number on
  the seam: simultaneously a count of magnitude-threshold events (`2d+c≥3`) and the exact
  correction term in the digit-sum recurrence. **Honesty boundary recorded in-file**: does
  NOT prove Erdős/Collatz, and pins the sharp negative that digit-2 ≠ carry-out (state
  `(1,0)` makes a 2 with carry 0; `doubleBase3 [1]=[2]` has `C=0`). So "digit field rich"
  (Erdős) and "size-events fire" (carry count) are genuinely different statements; the
  conservation law is the exact provable relation, not an identity of the two faces.
- **SWING #5b — telescoped closed identity (same file, axiom-clean).** Iterating the per-step
  recurrence `s_{j+1}=2s_j−2C_j` from `s_0=1` collapses to ONE equation:
  **`s₃(2^n) + 2·Σ_{j<n} 2^{n-1-j}·C_j = 2^n`** (`digitSum_base3_two_pow`; CA-list form
  `digitSum_two_pow_closed`; weight recurrence `weightedCarries_succ : W(n+1)=2W(n)+C_n`).
  Digit face on the left, magnitude face (`2^n`) on the right, carry weights the coupling.
  The geometric weight `2^{n-1-j}` = an early carry survives more doublings, so costs more
  magnitude (a carry's "price" is set by *when* it fires). **Numerics** (`#eval`, identity
  exact for all n tested): `s₃(2^n)` is tiny (n=8→4, n=11→10) while `W(n)≈2^{n-1}`
  (n=11→1019≈2^10), so in `2^n = s₃ + 2W` the digit-sum term is a vanishing correction —
  **quantifies that base-3 doubling is overwhelmingly carries.**

## Path 2 — One-constant effectivity hub ✅ BANKABLE

The family shares ONE bottleneck: an effective lower bound on `|2^L−3^n|` (Baker /
irrationality measure `μ(log₂3) ≲ 5.1`).

- **Lean** (`Effectivity.lean`, 0 sorries): proved arrow
  **`abs_cycleGap_le_cycleR`: for any cycle (x≥1, `x·gap = R(e)`), `|2^L−3^n| ≤ R(e)`** —
  so a gap *lower* bound forces `R(e)` (the whole cycle) large (the Eliahou mechanism).
  Plus `gapZ`, `cycleGap_eq_gapZ`, the bottleneck `EffectiveGapLowerBound`, and the
  hub consequence `cycleR_ge_of_gapBound`.
- **Honesty**: the *routing* is proved; the analytic core (a good `μ`, Baker constants)
  is the external input, not reproved. Value = the machine-checked dependency star with
  one constant at the center (Collatz cycles ← gap → Pillai / Erdős-leading-digit).

## Path 3 — `{(3/2)^n mod 1}` as shared substrate ❌ NULL (clean negative)

Tested whether `{(3/2)^n}` (= the gap object `3^n/2^n`) governs both Erdős and Collatz
deviations (`path3_threehalves.py`, n≤1500).

- `corr( #2s(2^n) , {(3/2)^n} ) = +0.027`; `corr( #2s(2^n) , {n log₂3} ) = +0.003`.
  Both ≈ 0. Erdős near-exceptions scatter across all `{(3/2)^n}` and `{n log₂3}` values.
- **Verdict**: `{(3/2)^n}` is NOT a shared low-order statistic. Confirms (again) the
  category error — no single fractional-part statistic bridges digit and magnitude faces.
  Honest null, exactly the difficulty-locus-predicted outcome.

## Path 4 — Is the digit structure automatic? ✅ WIN (clean Sturmian result)

Low digits ARE automatic (periodic, primitive root — `Equidistribution.lean`). The
**leading** base-3 digit is the question (`path4_leading_digit.py`, n≤4000).

- Leading digit ∈ {1,2}, governed by `{n·log₃2}`: density of digit-1 = **0.6308 ≈
  log₃2 = 0.6309**. Factor complexity **p(m) = m+1 exactly for m=1..17** ⟹ the sequence
  is **Sturmian**.
- Sturmian + irrational rotation `log₃2` ⟹ **NOT eventually periodic, NOT automatic**
  (Cobham). So the high-digit face of `2^n` is provably non-automatic.
- **Verdict**: pins Erdős's structural home — the automata/Cobham face (face 2),
  non-automatic territory. Explains *why* low-digit (automatic/periodic) methods can't
  reach it. The cleanest standalone finding of the sweep.

## Meta-conclusion

The genuine 2↔3 relationships are at the **interfaces**, not between the faces:
1. the **carry process** (magnitude↔digit interface) — Path 1,
2. one **Diophantine bottleneck** routing to all magnitude consequences — Path 2,
3. the digit face is **Sturmian / non-automatic** — Path 4.
The naive "shared fractional-part statistic" bridge fails — Path 3.

All four consistent with the three-faces model. No grand unification (still a category
error), but three real, formal, interface-level relationships + one honest null. Lean:
`Carry.lean`, `Effectivity.lean` (0 sorries each); scripts `path{1,3,4}_*.py`,
`erdos_lowdigit.py`.

## Follow-up threads ("do them all") — 2026-05-28, same session

Trevor: deepen each. Results (full `Erdos` builds clean, 0 sorries, 5 axioms):

**Thread 2 — Path 1 global bridge (`Carry.lean`, proved):**
- `doubleDigit_carry_lt_two`: the doubling CA preserves a `{0,1}` carry (d<3,c<2 ⟹ carry<2).
- **`two_mem_doubleAux_carry_made`**: every `2` in a doubled valid digit list is
  carry-made — comes from a `(1,0)`/`(2,1)` carry state. The global "2s are carry-made"
  lemma, by induction threading the carry invariant. (The `iterCA = canonical digits`
  bridge is left open — needs leading-nonzero canonicality; noted as the remaining gap.)

**Thread 3 — Path 2 concrete Baker constant (`Effectivity.lean`, axiom + derivation):**
- `baker_gap_lower` (axiom, cited `μ(log₂3) ≲ 5.1`): an effective threshold `N₀` past
  which `3^n/(L+1)^6 ≤ |2^L−3^n|`. **Existence form** — does NOT assert false small-case
  values (the bound genuinely fails for tiny n; honesty rail).
- **`cycleR_ge_baker`** (proved from the axiom + `abs_cycleGap_le_cycleR`): every genuine
  cycle with `n ≥ N₀` has `R(e) ≥ 3^n/(L+1)^6 → ∞` — effective "no small cycle", routed
  through one cited constant.

**Thread 1 — Path 4 Sturmian in Lean (`Sturmian.lean`, partial — honest boundary):**
- **`leadingDigit_mem`** (proved): the leading base-3 digit of `2^n` is `1` or `2`
  (via `digits_lt_base` + `getLast_digit_ne_zero`). `leadingWord` def + hand-verified
  singletons (`2¹,2³,2⁴,2⁶`).
- **NOT Lean-proved (documented)**: the Sturmian complexity `p(m)=m+1` and
  non-automaticity — needs irrational-rotation + factor-complexity machinery absent from
  mathlib. Recorded as the established (script-verified) finding, the honest limit.

**Caught & fixed mid-thread**: I first asserted `leadingWord 10 = [2,1,2,2,1,2,1,2,2,1]`
by `decide` from *guessed* values (wrong — `2⁴=121₃` leads with 1). Replaced with
hand-verified singletons. (Fabrication-risk self-catch, logged.)

Axioms now in Erdos/: abc, pillai, catalan, furstenbergStiffness, baker_gap_lower — all
classical/open inputs, none fake-proved. New modules `Carry`, `Effectivity`, `Sturmian`.
