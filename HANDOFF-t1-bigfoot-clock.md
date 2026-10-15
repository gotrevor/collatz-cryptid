# HANDOFF: T1, Bigfoot's parity clock and the engine census (2026-10-15)

Kickoff: `KICKOFF-2026-10-15-t1-bigfoot-clock.md`.  The write-up is in
`notes/32-bigfoot-clock-2026-10-15.md`.  All four targets are done, with proofs complete; no
`native_decide` and no new axioms.

| Target | Result | Declarations |
|---|---|---|
| 1. Parity clock | `b_{n+2} ≡ b_n + 1 (mod 2)` from any state; 4-phase clock on the orbit; `c = 2` at phases 0, 3 | `Dyn.step_step_parity`, `Dyn.parity_clock`, `Dyn.orbit_b_mod_two`, `Dyn.orbit_c_phase` (`Bigfoot/Clock.lean`) |
| 2. Reduced map | Bigfoot is `Hydra 32 24 bigfootH bigfootW (10, 2)` in int-y1's schema (`X = 4b + 3c`); block map `b ↦ 512⌊b/162⌋ + g₄`; drift `+1/6` per step (`Σ w₄ = 54/81`); LegionMammal978's table proved verbatim (**prior work**) | `Dyn.nonhalt_iff_hydra`, `Dyn.step4_block`, `Dyn.blockW_sum`, `Dyn.step4_legion` |
| 3. Census | Antihydra is `A 3`; #323 is `A 1`; BB(2,5) Hydra is `H` from 3 with the mirrored walk (substitution is prior work); **#323 and Hydra share the orbit `H^n(3)`**; `A 0`, `A 4` halt; #218 is the `K = ⌊4u/3⌋` orbit of 4.  Bigfoot's block map has no affine conjugacy to `K⁴` (paper + computed) | `Census.lean` |
| 4. Gate | The increment is local, the counter is not (`j ≤ 8`), so the verdict is **costume**.  The crux is decoded: `KPosCascade ↔ Margin2` (`a ≥ 2` at `b ≡ 2, 5 mod 6`), and `Margin2 → nonhalt` | `Dyn.walk_local`, `Dyn.a_not_local` (`Gate.lean`); `segment`, `kPosCascade_iff_margin2`, `margin2_nonhalt` (`V6Bridge.lean`) |

Open, in `src/` but outside this kickoff's scope: `V6KPos.k_at_9_ge_2_orbit`,
`k_at_3_ge_2_orbit` (= `Margin2`, the holdout with margin 2), and `Reduction.sim`.  The
`V6KPos.lean` docstring still says "equivalent to InvariantA / the holdout".  `V6Bridge.lean`'s
docstring gives the exact relation; per the kickoff I did not edit the older text.

Possible next steps (none required by the kickoff):
* `nonhalt → Margin2`?  It is open as mathematics, the same wall.  A *refutation* is impossible
  numerically (min `a` at `b ≡ 2, 5` is 3 over `10⁵` steps).
* Phase-0 `b ≡ 1 (mod 4)` (LegionMammal's `4β + 1`): `g₄ ≡ 1 (mod 4)` makes it a two-line
  corollary once a halting-agnostic version of `step4_block` exists (`b`-dynamics ignores `a`).
* Folklore check on the bbchallenge Discord (`#bb3x3`, `#bb-fractran`) for the parity lemma and the
  #323/Hydra shared orbit; this needs a host session (`ON-LINE-REQUEST.md`).
