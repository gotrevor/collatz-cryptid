/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.GoodsteinTM.Defs

/-!
# Computed checks

The Lean machines are the JSON machines (every (state, symbol) entry agrees), and the small seeds
halt after exactly the step counts `tools/goodstein_tm/test_halt.py` reports.
-/

namespace GoodsteinTM

theorem machine_four_eq_json : ∀ e ∈ json4, machine (cellsOf [1, 2, 3]) e.1 e.2.1 = e.2.2 := by
  decide +kernel

theorem machine_sixteen_eq_json :
    ∀ e ∈ json16, machine (cellsOf [1, 2, 3, 4]) e.1 e.2.1 = e.2.2 := by
  decide +kernel

/-- Halted after exactly `n` steps. -/
def haltsAt (t : List ℕ) (n : ℕ) : Bool :=
  match stepN (machine (cellsOf t)) n start with
  | some c => (machine (cellsOf t) c.state c.head).isNone
  | none => false

theorem haltsAt_one : haltsAt [1] 23 = true := by decide +kernel
theorem haltsAt_two : haltsAt [1, 2] 171 = true := by decide +kernel
theorem haltsAt_three : haltsAt [1, 2, 1] 285 = true := by decide +kernel
theorem not_haltsAt_three : haltsAt [1, 2, 1] 284 = false := by decide +kernel

end GoodsteinTM
