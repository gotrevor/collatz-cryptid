import Collatz.Holdout153.Machine

/-!
# The Holdout 153 hypothesis

Unlike Bigfoot, no public parametric reduction exists for this machine
(as of May 2026). Quick_Sim auto-discovers 16 parametric rules
(`notes/06-holdout153-rules.md`), but reducing them to a clean
finite-dimensional dynamical system — the analogue of Bigfoot's
`A(a, b, c)` — is open work.

So the hypothesis here is stated at the TM level only. Once Phase 2
produces a parametric reduction, we'll add a `Dyn` and a
dynamics-level hypothesis paralleling Bigfoot's pair.
-/

namespace Collatz.Holdout153

/-- **Holdout 153 hypothesis**: the Holdout 153 TM does not halt on
blank tape.

A dynamics-level restatement, modulo the parametric reduction, is
Phase 2 of the project plan. -/
def Hypothesis : Prop :=
  BB.NeverHalts machine BB.Cfg.blank

end Collatz.Holdout153
