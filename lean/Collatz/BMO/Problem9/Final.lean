/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.FinalBudget

/-!
# BMO #9: every `G` call returns

`Closure.G_returns_of` discharged by the budget `FinalBudget.budget`.
-/

namespace BMO9.Final

theorem G_returns : ∀ k t, ∃ e m, Prefix.Exec e (Prefix.G (k+1) (1+2*t)) [m] :=
  Closure.G_returns_of FinalBudget.budget

end BMO9.Final
