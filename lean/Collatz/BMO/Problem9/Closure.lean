/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Prefix
import Collatz.BMO.Problem9.Block
import Collatz.BMO.Problem9.CheckTable

/-!
# BMO #9, port of Rocq `Module Closure` (BMO9.v lines 2659-2740)

`G_returns`: every `G (k+1) (1+2t)` prefix safely returns to a singleton.  Rocq proves this by
strong induction on table entries (`all_good`), with `CheckTable.base_structured` for
`k ≤ 65536` and `FinalBudget.budget` above.  Not yet ported.
-/

namespace BMO9.Closure

open Prefix

/-- **Open crux.**  Rocq `Closure.G_returns` composed with `FinalBudget.budget`. -/
theorem G_returns : ∀ k t, ∃ e m, Exec e (G (k+1) (1+2*t)) [m] := by
  sorry

end BMO9.Closure
