import Collatz.BB.SweepPDA
import Collatz.WilyCoyote.Machine
import Collatz.WilyCoyote.Hypothesis

/-!
# Wily Coyote as a sweep PDA — trivial realization

Same shape as `Collatz.FatCoyote.SweepPDA`: lift the TM directly into
the abstract `BB.SweepPDA` framework. `MacroCfg := BB.Cfg`,
`step := BB.step machine`, `init := BB.Cfg.blank`.

A *refined* realization for Wily Coyote could in principle bake in the
LEFT-side saturation finding from `notes/20` — `MacroCfg` could include
a single fixed left-bootstrap word and an N-counter for the left-side
periodic body. But the RIGHT bootstrap is still empirically open
(slowing, not saturated at 10M), so a fully concrete `MacroCfg` would
either need to leave the right side opaque or commit to a finite type
that 10M data does not yet justify.
-/

namespace Collatz.WilyCoyote

open BB

/-- The trivial sweep-PDA realization of Wily Coyote. -/
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

/-- **Equivalence**: the Wily Coyote hypothesis stated at the (trivial)
sweep-PDA level is the *same proposition* as the TM-level hypothesis. -/
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

end Collatz.WilyCoyote
