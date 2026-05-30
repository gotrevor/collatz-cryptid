import Collatz.WilyCoyote.Machine

/-!
# The Wily Coyote hypothesis

Stated at the TM level. There is no known parametric reduction. Per
`notes/13`, the bounded-length hypothesis was refuted at 10M loops (max
word length grows 24 → 33). Per `notes/20`, the 10M-loop reversal-burn
shows LEFT bootstrap saturated at 1 word and RIGHT bootstrap slowing
but not yet saturated (novelty ratio 0.40 at peaks/valleys, slope 0.28).

531 may admit a finite-state-counter reduction if the RIGHT bootstrap
saturates with more data — open question requiring a 100M-loop burn or
a structural probe of the R-bootstrap word language. See
`Collatz/BB/SweepPDA.lean` for the abstract framework and
`Collatz/WilyCoyote/SweepPDA.lean` for the trivial realization.
-/

namespace Collatz.WilyCoyote

/-- **Wily Coyote hypothesis**: the Wily Coyote TM (BB(3,3) holdout 531)
does not halt on blank tape.

Empirically verified through 10M macro-loops (~30M TM-steps). Standard
deciders return empty (Andrew Ducharme exhaustive sweep, Feb-Mar 2026). -/
def Hypothesis : Prop :=
  BB.NeverHalts machine BB.Cfg.blank

end Collatz.WilyCoyote
