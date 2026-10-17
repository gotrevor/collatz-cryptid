# PENDING_WORK (t4-haar-rate)

2026-10-17 lap 4: the crux has a residue-free form and a parity form, both in Lean
(`lean/Collatz/Antihydra/HaarShift.lean`):
* `crossEnergy_eq_shiftKernel`: Λ_N is the value at 1 of an explicit integer recursion;
* `crossEnergyBounded_iff_parity`: the crux holds iff the partial sums of the weighted parity
  correlations `P_n = (𝒦^n χ)(1)` are bounded, via `Λ_N = 1 + (p₀−p₁+p₂)² ∑_{n<N} P_n`;
* `kernelOp_parity`: odd parents cancel exactly;
* `crossEnergy_add_sub_le`: the multiscale total-variation form of condition (S).
Numerics (notes/37 §9): `P_n/Λ_n` decays slowly (about `e^{−0.07n}`) and oscillates, and
`TV_{n,k} ≈ 0.18 e^{−0.10n+0.33k}`.  No proof mechanism was found.  Every reformulation needs
exponential equidistribution of the chain `δ ↦ (3δ+e)/2` mod `2^k`, and the known AC theorems
need far more entropy excess than the ≤ 5% available.  DIRECTION's stop rule applied: obstruction
recorded, `box done`.
Next attack, if the track reopens: prove `ParityCorrSummable candidate`.  The most concrete
sub-target is exponential decay of `P_n` for the candidate.  A 3-adic/2-adic CRT decoupling
of the forward measure (real envelope × 3-adic pattern) is the one heuristic mechanism; it has
not been made quantitative.

2026-10-17 lap 3 (review): the crux now has a minimal form, `MomentBounded candidate (1/32)`.  It
is equivalent to bounded shift moments, and the headline follows from it
(`haarRate_le_eight_twentyfifths_of_momentBounded`).  (C1) is only sufficient: it adds a
Diophantine condition at 1.  Hardness: the 2-adic analogue of an open AC problem (notes/37 §8).
Next, in order:
1. Lean: the integer shift recursion `crossEnergy p N = crossShift p N 1`, with
   `C_{N+1}(2u) = 2[π₀C(3u) + π₂(C(3u+1)+C(3u−1))]` and `C_{N+1}(2u+1) = 2π₁[C(3u+1)+C(3u+2)]` for
   `δ ≥ 1`.  The proof expands `rho_succ_even/odd` and reindexes with `sum_range_pow_affine`.
2. Numerics for condition (S) (notes/37 §8): `max |F_n(ξ)|` over `ξ ∈ 2^{−k}ℤ∖0` against `n, k`.
3. Stop rule (DIRECTION.md): if (S) shows no mechanism, record the obstruction and `box done`.

2026-10-17 lap 2: Theorems A and B are proved in Lean.  The headline
`haarRate_le_eight_twentyfifths` is sorry-free and conditional only on `CrossEnergyBounded
candidate` (the crux).  Next attack on the crux: Lean statement of the shift recursion
(`crossEnergy = lam 1`), then the increment structure `T_k` and the parity cancellation.  See
HANDOFF lap 2.

2026-10-17: crux advanced.  `a_* ≤ p₁+2p₂` is reduced (spine decomposition, notes/37 Thms A/B)
to one open hypothesis `CrossEnergyBounded p` (`HaarDigitRate.lean`): the adjacent `L²`
cross-energy `∫ρ_N(y)ρ_N(y+1)dm` of Fornet's iid law is bounded.  Numerics are flat (0.547 for
(18,6,1)/25, N ≤ 46); the known-false multiplier-1 sibling diverges.  Next attack: formalize
`moment_bound` (finite), then (C1) via equidistribution of the shift chain `δ_j mod 2^k`.

# PENDING_WORK (t1-bigfoot-clock)

2026-10-15: the kickoff scope is complete; see `HANDOFF-t1-bigfoot-clock.md`.
Advance on the crux this lap: `KPosCascade` (the repo's Bigfoot crux) is now *proved equivalent*
to `Margin2` in Ligocki coordinates (`V6Bridge.kPosCascade_iff_margin2`).  It is a single-orbit
walk statement whose counter is not digit-local (`Gate.a_not_local`), so it is the open problem
in costume.  Next attack, if anyone reopens Bigfoot: there is none within the horizon.  Any
proof must control the partial sums of `walkInc (b_n mod 6)` along one orbit (the Antihydra-type
wall).
