import Collatz.BB.SweepPDA
import Collatz.FatCoyote.Machine
import Collatz.FatCoyote.Hypothesis

/-!
# Fat Coyote as a sweep PDA — trivial realization

This is the **minimal** realization: we lift the TM directly into the
abstract `BB.SweepPDA` framework, with `MacroCfg := BB.Cfg`,
`step := BB.step machine`, `init := BB.Cfg.blank`.

It does *not* extract head-signature or sweep-phase structure. A more
refined realization would set
`MacroCfg := head_sig × bootstrap × N_left × phase`,
but constructing that requires proving the empirically-observed
sweep-PDA structure of 397 — beyond the current scaffold and not what
`notes/20` rules in. The 10M data shows 397's reachable bootstrap is
unbounded; encoding that faithfully requires the opaque-MacroCfg
posture this trivial realization adopts.

The payoff: a statement-level `sweepPDA.NeverHalts` that is provably
equivalent to `BB.NeverHalts machine BB.Cfg.blank`. Same hypothesis,
different vocabulary — and the vocabulary now has a Lean-side home for
future refinement.
-/

namespace Collatz.FatCoyote

open BB

/-- The trivial sweep-PDA realization of Fat Coyote. -/
def sweepPDA : BB.SweepPDA where
  MacroCfg := Cfg
  step := BB.step machine
  init := Cfg.blank

/-- Orbit of the trivial sweep-PDA realization equals `BB.stepN` of the
underlying TM. Proved by induction on `n`. -/
theorem sweepPDA_orbit_eq_stepN (n : ℕ) :
    sweepPDA.orbit n = BB.stepN machine n Cfg.blank := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change (sweepPDA.orbit k).bind (BB.step machine)
         = (BB.stepN machine k Cfg.blank).bind (BB.step machine)
    rw [ih]
    rfl

/-- **Equivalence**: the Fat Coyote hypothesis stated at the (trivial)
sweep-PDA level is the *same proposition* as the TM-level hypothesis.

The trivial realization adds no new information; it just gives the
SweepPDA-level vocabulary a Lean-side anchor for FatCoyote. Future
refined realizations would change the LHS without changing the RHS. -/
theorem sweepPDA_neverHalts_iff_TM :
    sweepPDA.NeverHalts ↔ Hypothesis := by
  unfold BB.SweepPDA.NeverHalts Hypothesis BB.NeverHalts
  constructor
  · intro h n
    rw [← sweepPDA_orbit_eq_stepN]
    exact h n
  · intro h n
    rw [sweepPDA_orbit_eq_stepN]
    exact h n

end Collatz.FatCoyote
