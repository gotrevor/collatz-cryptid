# PENDING_WORK (t4-haar-rate)

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
