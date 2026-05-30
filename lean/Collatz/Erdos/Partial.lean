import Collatz.Erdos.Basic
import Collatz.Erdos.Conjecture

/-!
# Partial results on Erdős's conjecture

* **Odd `n`**: `2^n % 3 = 2`, so the lowest base-3 digit is already `2`.
* **Known exceptions** (`n ∈ {0, 2, 8}`): verified by `decide`.

The conjecture's remaining content is the **even** `n > 8` case.
-/

namespace Collatz.Erdos

/-- The odd half of Erdős's conjecture is trivial: every odd `n` has `2` as
the lowest base-3 digit of `2^n`. -/
theorem erdos_odd {n : ℕ} (hn : n % 2 = 1) : 2 ∈ Nat.digits 3 (2 ^ n) := by
  apply two_mem_digits_three
  · exact Nat.pos_of_ne_zero (by
      intro h
      exact absurd (Nat.pow_eq_zero.mp h).1 (by decide))
  · exact two_pow_odd_mod_three hn

/-- Erdős reduces to the even case: it suffices to prove it for even `n > 8`. -/
theorem erdos_of_even (h : ∀ n : ℕ, 8 < n → n % 2 = 0 → 2 ∈ Nat.digits 3 (2 ^ n)) :
    ErdosConjecture := by
  intro n hn
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · exact h n hn he
  · exact erdos_odd ho

/-- The three known exceptional powers `2^0 = 1`, `2^2 = 4`, `2^8 = 256`
each have base-3 representation using only `0`s and `1`s. -/
theorem erdos_exceptions_no_two :
    NoTwoInBase3 (2 ^ 0) ∧ NoTwoInBase3 (2 ^ 2) ∧ NoTwoInBase3 (2 ^ 8) := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold NoTwoInBase3; decide)

/-- Sanity check: the conjectural lower bound `n > 8` is tight at `n = 8`. -/
theorem two_pow_eight_no_two : NoTwoInBase3 (2 ^ 8) := by
  unfold NoTwoInBase3; decide

end Collatz.Erdos
