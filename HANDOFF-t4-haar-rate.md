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
* **Lap 2: no `sorry` left in `HaarDigitRate.lean`.**  `moment_bound`, `candidate_spineRatio_lt_one`
  and `haarRate_le_of_crossEnergyBounded` are proved, so `haarRate_le_eight_twentyfifths` is
  axiom-clean.  Its only hypothesis is `CrossEnergyBounded candidate`, the crux.

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

## Checkpoint (lap end, 2026-10-17)

Branch `wip/t4-haar-rate`, HEAD `47d0860`.  The tree is clean, apart from the untracked
`CLAUDE.local.md` (not ours to commit).  The scratch dir `tmp/` holds copies of the numerics
programs.  It is not committed; canonical copies are in `tools/sandbox/haar_digit_rate/`.

Unstarted idea for the next lap, crux-side.  Since `L1 = α·1_odd + β·1_even`,
`Λ_{n+1} − Λ_n = ((β−α)/2)·⟨m_n, (−1)^δ⟩`, where `m_n` is the forward shift measure from `δ = 1`.
So (C1) is equivalent to bounded partial sums of the parity correlations `(L^j χ)(1)`,
`χ(δ) = (−1)^δ`.  Plan: compute this increment sequence for `n = 20..50` and test whether it
decays (a spectral mechanism) or oscillates.  Record the result in notes/37 §6 and in the
`CrossEnergyBounded` docstring.

## Lap 2 (2026-10-17)

Commits `14d516d` (Theorem A), `626c03f` (q(1/32) < 1), `5db49ff` + `f4a2bf0` (Theorem B).
Theorem B carries `set_option maxHeartbeats 2000000` (elaboration of the big assembly).

Crux findings this lap (none of them proves (C1) yet):
* **Fornet's finite-memory MDP route is out of reach.**  Fresh numerics, float relative value
  iteration in `tmp/mdp/lam.c`, give `λ_L = 0.3789 (16), 0.3702 (20), 0.3634 (24)`.  `λ_22`
  matches Fornet's certified `0.36661`.  The decay is slower than `log L / L`, so `λ_L < 1/3`
  needs `L ≳ 60` bits, beyond direct computation.
* **Gibbs-variational lower bounds on the quenched free energy give nothing past a policy's own
  cost.**  Any randomized policy that beats 1/3 through its entropy would sit above the
  annealed entropy curve's tangent line.  Not recorded in Lean yet.
* **Exact increment formula** (checked numerically against `cross_energy_p.c` to 6 digits):
  `Λ_N = 1 + ∑_{k≤N} T_k` with
  `T_k = ∑_{η odd mod 2^k} cos(2π 3^k η/2^k) ∏_{i≤k} π̂(3^{i−1}η/2^i)`.
  The absolute mass grows like `1.155^k` while `|T_k| ≈ 1e-3` at `k ≈ 40`.  `|T_k|` decays slowly
  and oscillates.
* **Parity-cancellation identity** `L*χ = 2(π₀ − 2π₂) χ₄`: the odd parents cancel exactly.
* **Integer picture.**  `W_j = R_j|_ℤ`: every integer has 1–2 backward predecessors and parity
  holds automatically.  `W_j` has a forced mod-3 pattern, so it is not smooth at unit scale.  The
  CRT heuristic (3-adic fine structure × 2-adic period) is the likely mechanism behind (C1).

Next: state the shift-recursion form of `crossEnergy` in Lean (`crossEnergy p N = lam p N 1`).
That makes (C1) an elementary integer-recursion statement, with `decide` anchors.  Then attack it
through the increment/parity structure.

## Checkpoint (lap 2 end, 2026-10-17)

Branch `wip/t4-haar-rate`, HEAD `65dc9e8`.  The tree is clean apart from the untracked
`CLAUDE.local.md` (not ours) and `tmp/` (scratch, not committed).  `tmp/mdp/` holds `lam.c`
(MDP gain), `tk.c` (the increment formula `T_k`) and `cand*.txt` (`Λ_N` up to N=44, plus a
45..52 background run).  `HaarDigitRate.lean` has no `sorry`.  The only open obligation is
`CrossEnergyBounded candidate`.  First task next lap: the Lean statement
`crossEnergy p N = lam p N 1` for the integer shift recursion.

## Lap 3 (2026-10-17, review lap)

Branch `wip/t4-haar-rate`.  Commit `babde70` adds the minimal crux:
* `MomentBounded`, `ShiftMomentBounded`, `shiftMomentPlus/Minus`, `moment_succ_le_shift`,
  `shiftMoment_le_moment`, `momentBounded_iff_shiftMomentBounded`, and
  `momentBounded_of_crossEnergyBounded`;
* `haarRate_le_of_momentBounded` (the old Theorem B body, which now needs only `MomentBounded`);
* `haarRate_le_eight_twentyfifths_of_momentBounded`.

All of these are axiom-clean (trust base only).  `DIRECTION.md` (CURRENT DIRECTIVE, stop rule)
and `STATUS.md` are new.  notes/37 §8 records the hardness assessment and condition (S).

Next: PENDING_WORK top entry.  First the integer shift recursion in Lean, then numerics for (S).
`tmp/` is scratch and not committed.

## Lap 4 (2026-10-17)

Commits `245f07f` (shift recursion), `2934324` (parity form), `25e3809` (multiscale bound, notes/37
§9).  New module `lean/Collatz/Antihydra/HaarShift.lean` (imported by `Collatz.Antihydra`):
`crossShift`, `pairLaw`, `shiftKernel`, `crossEnergy_eq_shiftKernel`, `kernelOp`, `parityCorr`,
`crossEnergy_eq_one_add_sum`, `crossEnergyBounded_iff_parity`, `kernelOp_parity`,
`parityCorr_succ`, `ParityCorrSummable` (open, docstring evidence),
`candidate_crossEnergyBounded_of_paritySummable`, `forwardMass`, `crossEnergy_add_eq`,
`crossEnergy_add_sub_le`.  All axiom-clean, with no `sorry`.  Numerics programs:
`tools/sandbox/haar_digit_rate/{parity_corr,fwd_tv,fwd_fourier}.c`.

Outcome: the DIRECTION stop rule fired.  There is no viable mechanism for (S) or (C1); notes/37 §9
records the obstruction.  `box done` signalled.

**Scope note for the host.**  `box done` reports 9 open sorries repo-wide.  None is on this
track: they sit in other tracks' modules (`Tao.lean`, `Korec.lean`, `Bigfoot/*`), outside the T4
kickoff.  `HaarDigitRate.lean` and `HaarShift.lean` have no `sorry`.  This run should be scoped
with `--done-when 'sorry-free:lean/Collatz/Antihydra/HaarShift.lean'` (or HaarDigitRate.lean).
