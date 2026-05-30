# 25 — Furstenberg stiffness axiom + the low-digit equidistribution seam 🪷

**Date**: 2026-05-28 (same session as notes/24). **Mode**: Lean formalization,
Trevor's two asks: (A) add a Furstenberg-style stiffness axiom and trace what it
buys for Erdős; (B) Lean the primitive-root / low-digit equidistribution, "the
seam where assuming-vs-proving has an actual seam."

Origin: the "is √2 normal?" conversation. √2 *itself* is irrelevant (it was an
analogy), but the **normality idea applied to the base-3 digits of 2ⁿ** is exactly
the Erdős face. The seam: **low digits provable, high digits open.**

## The seam, sharpened

The lowest base-3 digit already splits Erdős (both halves were already in the repo,
`Basic.lean` + `Partial.lean`):
- **odd n**: `2ⁿ % 3 = 2` ⟹ low digit is 2 ⟹ Erdős holds (`Partial.erdos_odd`). DONE.
- **even n**: `2ⁿ % 3 = 1` ⟹ low digit 1 ⟹ a 2 must appear in the HIGH digits.
  **This is the entire open content** (normality / Furstenberg regime).

So the axiom's real job is only the even tail; the odd case needs nothing.

## (A) Furstenberg stiffness axiom — `Axioms.lean` (Axiom 4)

```lean
def FurstenbergDigitStiffness : Prop :=
  ∀ v : ℕ, v < 3 → ∃ N, ∀ n, N < n → v ∈ Nat.digits 3 (2 ^ n)
axiom furstenbergStiffness : FurstenbergDigitStiffness
```
The digit-level shadow of ×2,×3 rigidity: every base-3 digit value eventually always
occurs in 2ⁿ. **Stronger than Erdős** (Erdős = the v=2 case). Traced consequences
(all sorry-free):
- `eventualErdos_of_stiffness` / `eventualErdos`: stiffness ⟹ `∃N, ∀n>N, 2∈digits 3 2ⁿ`.
- `erdos_of_tail_and_window`: **full Erdős = finite window (8,N] + infinite tail**
  (a split of ℕ, NOT a reduction to computation). Only the window is finite; the
  tail IS Erdős. The axiom supplies the tail by *assumption* and *ineffectively*
  (`∃N`, no computable value), so there's no concrete N to compute up to — the bare
  axiom proves only `eventualErdos` (n>N form), not full Erdős (n>8 form). Missing
  piece = an effective exception bound (unknown). Same effectivity wall as abc.
  **(Overclaim corrected 2026-05-28 after Trevor's "why hasn't this been computed?")**

⚠️ **Honesty note (in the docstring)**: this does NOT reduce the open content, it
*names* it. Deriving Erdős from it is "assume the deep pseudorandomness, recover the
instance," not external leverage. The genuinely deep parent is the topological/measure
×2,×3 rigidity; this is its digit-level form at the altitude that plugs into Erdős.
Sits beside abc/pillai/catalan as the 4th axiom.

## (B) Low-digit equidistribution — `Equidistribution.lean` (new, 0 sorries)

The *provable* half, quantifying the `(2/3)ᵏ` heuristic:
- `two_pow_coprime_three_pow`: 2ⁿ always a unit mod 3ᵏ.
- `two_pow_even_mod_three`: even n ⟹ low digit 1 (the seam statement).
- **2 is a primitive root mod 3ᵏ**, machine-checked k≤4 via image-card =
  φ(3ᵏ)=2·3^{k-1} (`((range period).image (i↦2^i : ZMod 3ᵏ)).card = period`),
  so 2ⁿ cycles through ALL units = perfect low-digit equidistribution.
  (mod_81 needs `set_option maxRecDepth 100000`.)
- **2-free density = ½·(2/3)^{k-1}**: `twoFreeOverPeriod k = 2^{k-1}` for k≤4
  (`twoFree_k1..k4` = 1,2,4,8). The geometric decay behind "finitely many exceptions".

General primitive-root fact = classical lifting (2 is a p.r. mod 3 and mod 9 ⟹ mod all
3ᵏ); mathlib has `ZMod.isCyclic_units_of_prime_pow` (cyclic) but not "2 is the
generator", so we verify computationally for k≤4. Companion script:
`~/personal/tools/sandbox/erdos_lowdigit.py` (the table: period=φ(3ᵏ), frac=½(2/3)^{k-1}).

### CAP RETIRED — `Lifting.lean` (next session, 2026-05-28, axiom-clean)
The "2 is a primitive root mod 3ᵏ" claim is now **general for all k**, no `decide` cap:
- **LTE core** `two_pow_witness`: `2^(2·3^j) = 1 + 3^(j+1)·u` with `3∤u`, i.e.
  `v₃(2^(2·3^j) − 1) = j+1` exactly. Proof = elementary binomial induction (cube the
  previous witness), **no `multiplicity`/`emultiplicity` API**. Corollaries
  `three_pow_dvd` (order divides 2·3^j) / `not_three_pow_dvd` (order exact).
- **Endgame** `orderOf_two_mod_three_pow (k≥1) : orderOf (2 : ZMod (3ᵏ)) = 2·3^{k-1}`.
  Bridge `pow_two_eq_one_iff` (ZMod power=1 ↔ ℤ divisibility) + divisor-lattice argument
  (2∤order ⟹ order∣3ᵏ contra via `2^{odd}≡−1 mod 3`; then `order=2·3^j`, force `j=m`
  via `not_three_pow_dvd`). All `#print axioms` clean (propext/choice/quot).
- The 2-free **density** `decide`s (`twoFree_k1..k4`) still cap at k≤4 — they'd need the
  count-of-2-free-units combinatorics on top. Only the primitive-root half is now general.

## Status

`lake build Collatz.Erdos`: clean, **0 sorries**. Axioms in Erdos/: abc, pillai,
catalan, **furstenbergStiffness** (new). The seam is now explicit in Lean: odd-n Erdős
proved, low-digit equidistribution proved (k≤4) + density quantified, even-n high-digit
content isolated and named by the Furstenberg axiom.

## Verdict (difficulty-locus honest)

We did not crack Erdős. We **formalized the boundary** between what multiplicative
independence gives you for free (low digits, odd n, the (2/3)ᵏ count) and what it
doesn't (high-digit pseudorandomness for even n). The Furstenberg axiom names the open
part precisely; the equidistribution module proves the closed part precisely. That
boundary *is* the deliverable — same spirit as notes/24's "the deep relationship is the
absence of one + the small true lemma."
