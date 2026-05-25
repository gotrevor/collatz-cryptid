import Mathlib.Tactic
import Mathlib.Logic.Function.Iterate

/-!
# The (slow) Collatz map

`T : ℕ → ℕ`, defined by
* `T n = n / 2`   if `n` is even
* `T n = 3 n + 1` if `n` is odd

`T 0 = 0` is a degenerate fixed point; positive-integer hypotheses live with
the theorems that need them.
-/

namespace Collatz

/-- The slow Collatz map. -/
def T (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

@[simp] theorem T_zero : T 0 = 0 := by decide
@[simp] theorem T_one : T 1 = 4 := by decide
@[simp] theorem T_two : T 2 = 1 := by decide
@[simp] theorem T_four : T 4 = 2 := by decide
theorem T_three : T 3 = 10 := by decide
theorem T_five : T 5 = 16 := by decide

/-- The trivial Collatz cycle: `1 → 4 → 2 → 1`. -/
theorem T_iter_three_one : T^[3] 1 = 1 := by decide

end Collatz
