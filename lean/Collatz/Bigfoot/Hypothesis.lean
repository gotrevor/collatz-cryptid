import Collatz.Bigfoot.Machine
import Collatz.Bigfoot.Dynamics

/-!
# The Bigfoot hypothesis (`Prop`-level)

Just the dynamics-level claim. The TM-level consequence
(`MachineNeverHalts`) and the reduction glue live in
`Collatz/Bigfoot/Reduction.lean`.
-/

namespace Collatz.Bigfoot

/-- **Bigfoot hypothesis** (Ligocki 2023): the (a, b, c) dynamics, started
from `A(2, 1, 2)`, never reaches the halting branch
(`a = 0 ∧ b % 6 = 2`).

Empirically verified for an astronomical number of iterations. The
dynamics are *Collatz-like*: `b` grows by roughly a factor of `8/6 = 4/3`
per step; `a` drifts via the mod-6 phase. -/
def Hypothesis : Prop :=
  ∀ n : ℕ, Dyn.orbit n ≠ none

end Collatz.Bigfoot
