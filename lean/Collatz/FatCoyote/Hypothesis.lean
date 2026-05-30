import Collatz.FatCoyote.Machine

/-!
# The Fat Coyote hypothesis

Stated at the TM level. There is no known parametric reduction. Per
`notes/15`, the clean Bigfoot-style (a, b, c) form is empirically refuted
at the 623-snapshot scale; per `notes/20`, the 10M-loop reversal-burn
quantitatively confirms the bbchallenge community's consensus that 397
has unbounded auxiliary state (valley novelty ratios 1.18-1.38 at 10M,
peak L-bootstrap 100% unique with slope 1.00). Any dynamics-level Lean
restatement therefore requires an *opaque* reachable-state type, not a
finite inductive — see `Collatz/BB/SweepPDA.lean` for the abstract
framework and `Collatz/FatCoyote/SweepPDA.lean` for the trivial
realization equivalence.
-/

namespace Collatz.FatCoyote

/-- **Fat Coyote hypothesis**: the Fat Coyote TM (BB(3,3) holdout 397) does
not halt on blank tape.

Empirically verified through 2.5M macro-loops (~7.5M TM-steps). Standard
deciders return empty (Andrew Ducharme exhaustive sweep, Feb-Mar 2026). -/
def Hypothesis : Prop :=
  BB.NeverHalts machine BB.Cfg.blank

end Collatz.FatCoyote
