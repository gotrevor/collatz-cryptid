import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Base-3 helpers for Erdős's conjecture on 2^n

Small lemmas about `2^n % 3` and about membership in `Nat.digits 3`.
-/

namespace Collatz.Erdos

/-- `2^n mod 3` cycles with period 2: it is 1 for even `n`, 2 for odd `n`. -/
theorem two_pow_mod_three (n : ℕ) :
    2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => decide
  | succ k ih =>
    have hpow : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hpow, Nat.mul_mod, ih]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
      · simp [hk, Nat.add_mod]

/-- For odd `n`, the lowest base-3 digit of `2^n` is `2`. -/
theorem two_pow_odd_mod_three {n : ℕ} (hn : n % 2 = 1) : 2 ^ n % 3 = 2 := by
  rw [two_pow_mod_three]; simp [hn]

/-- If a positive natural has remainder `r < b` when divided by `b ≥ 2`,
    then `r` appears in its base-`b` digit list. -/
theorem mem_digits_of_mod {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    n % b ∈ Nat.digits b n := by
  rw [Nat.digits_def' hb hn]
  exact List.mem_cons_self

/-- `2 ∈ digits 3 m` whenever `m > 0` and `m % 3 = 2`. -/
theorem two_mem_digits_three {n : ℕ} (hn : 0 < n) (h : n % 3 = 2) :
    2 ∈ Nat.digits 3 n := by
  have := mem_digits_of_mod (b := 3) (by decide) hn
  rw [h] at this; exact this

end Collatz.Erdos
