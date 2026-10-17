# HANDOFF: T4, Haar-mean base-3/2 digit rate (2026-10-17)

Kickoff: `KICKOFF-2026-10-17-t4-haar-rate.md`.  Paper: `notes/37-haar-rate-second-moment-2026-10-17.md`.
Lean: `lean/Collatz/Antihydra/HaarDigitRate.lean`.

## State

* **Target 2 (Lean finite core): done.**  `V` + Bellman (`V_succ_even/odd`), faithfulness
  (`V_isLeast`), periodicity (`V_add_pow_mul`, `V_mod`), anchors `sumV_four = 31`,
  `sumV_eight = 936` (`decide`, axioms: propext only), `Z`, `rho`, `paley_zygmund` (proved).
* **Target 1 (paper): reduced to a precisely stated obstruction.**  The kickoff's barrier second
  moment was replaced by a spine decomposition of `μ_p`'s density martingale (notes/37 §2).
  Theorem A: `∫ρ_N^{1+s} ≤ q^N + r∑ q^j Λ_{N-1-j}^s`, where `Λ_n = ∫ρ_n(y)ρ_n(y+1)dm`.
  Theorem B: bounded `Λ` and `q(s) < 1` (entropy > log 2) give `a_* ≤ p₁+2p₂`.
  For Fornet's candidate (18,6,1)/25 that is `a_* ≤ 8/25`.
* **Crux (open): `CrossEnergyBounded`** (Λ bounded).  Numerically flat at every law tested,
  `N ≤ 48`.  Control: the multiplier-1 sibling gives growth `1.0137^N`.  notes/37 §3.
* Sorries in `src` (all disclosed, on-path):
  `moment_bound` (90%), `haarRate_le_of_crossEnergyBounded` (85%),
  `candidate_spineRatio_lt_one` (99%, numeric rpow).

## Next

1. Formalize `moment_bound` (finite sums over `{0,1,2}^N`: residue map `r_w`, the spine identity,
   tail independence, Jensen/subadditivity for `x^s`).  It is pure finite combinatorics.
2. `candidate_spineRatio_lt_one`: bound `rpow` at `s = 1/32` (e.g. via `Real.rpow` monotone
   bounds from `x^{1/32}` with 32nd powers of rationals).
3. Crux attack (C1): equidistribution of `δ_j mod 2^k` for `k ≤ j log₂(3/2)` along the
   Feynman–Kac chain (notes/37 §6).  Also try a real-size + residue potential with `|δ|` growth.
4. `haarRate_le_of_crossEnergyBounded`: Hölder + Chebyshev + block-commitment bijection
   (Fornet OE1/AC1, finite).

Numerics: `tools/sandbox/haar_digit_rate/cross_energy*.c`.  The box has no libc headers.  Compile
with the toolchain's `leanc` (prototypes inline): `leanc -O3 -c f.c && leanc f.o -o f -lm`.
