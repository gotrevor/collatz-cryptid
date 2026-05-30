import Mathlib.Tactic
import Collatz.Erdos.Basic
import Collatz.Erdos.Conjecture
import Collatz.Erdos.Axioms

/-!
# Erdős's conjecture, term-count by term-count

If `2^n` has no `2` in base 3, then `2^n = ∑ 3^{a_i}` for some distinct
exponents `a_i`.  The known Erdős exceptions correspond to specific
term counts:

| Erdős exception `N` | `2^N` as sum of distinct 3-powers | terms `k` |
|---|---|---|
| `N = 0` | `1`                                    | 1 |
| `N = 2` | `3 + 1`                                | 2 |
| `N = 8` | `243 + 9 + 3 + 1`                      | 4 |

This file proves Erdős case-by-case in `k`:

* **k = 1** — `two_pow_eq_one_term_three_pow`: elementary.
* **k = 2** — `two_pow_eq_two_term_three_pow_sum`: uses **Catalan**
  (axiomatized in `Erdos/Axioms.lean`).
* **k = 3** — `two_pow_ne_three_term_three_pow_sum`: elementary
  (mod-8 argument).
* **k ≥ 4** — open / future work.  The case `k = 4` is exactly where
  the Erdős exception `N = 8` (i.e. `2^8 = 243 + 9 + 3 + 1`) lives,
  so a clean Erdős-for-`k=4` theorem would have a non-vacuous unique
  witness.
-/

namespace Collatz.Erdos

/-! ## Shared helpers -/

/-- `3` does not divide `2^n` for any `n`. -/
theorem three_not_dvd_two_pow' (n : ℕ) : ¬ (3 : ℕ) ∣ 2 ^ n := by
  intro hd
  have hcop : Nat.Coprime 3 (2 ^ n) :=
    Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2)
  have h3_one : (3 : ℕ) ∣ 1 := by
    have hgcd := Nat.dvd_gcd (dvd_refl 3) hd
    rw [hcop] at hgcd
    exact hgcd
  exact absurd h3_one (by decide)

/-- `3^a mod 8 = 1` if `a` even, `= 3` if `a` odd. -/
theorem three_pow_mod_eight (a : ℕ) :
    (3 : ℕ) ^ a % 8 = if a % 2 = 0 then 1 else 3 := by
  induction a with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have hk1 : (k + 1) % 2 = 1 := by omega
      simp [h, hk1]
    · have hk1 : (k + 1) % 2 = 0 := by omega
      simp [h, hk1]

/-! ## k = 1: elementary -/

/-- **Erdős for 1-term sums** (elementary).

If `2^n = 3^a`, then `n = 0` and `a = 0`. -/
theorem two_pow_eq_one_term_three_pow {a n : ℕ} (h : 2 ^ n = 3 ^ a) :
    n = 0 ∧ a = 0 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · refine ⟨?_, ha⟩
    rw [ha, pow_zero] at h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact hn
    · exfalso
      have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
      simp at h2
      omega
  · exfalso
    apply three_not_dvd_two_pow' n
    rw [h]
    exact dvd_pow_self 3 ha.ne'

/-! ## k = 3: elementary (mod-8 argument) -/

/-- **Erdős for 3-term sums** (elementary, no axiom).

There is no `(a, b, c, n)` with `c < b < a` and `2^n = 3^a + 3^b + 3^c`.

Proof: `3 ∤ 2^n` forces `c = 0`, reducing to `2^n = 3^a + 3^b + 1` with
`a > b ≥ 1`.  For `n ≥ 3`, `2^n ≡ 0 (mod 8)` but `3^a + 3^b + 1 ∈
{3, 5, 7} (mod 8)`.  For `n ≤ 2`, the RHS is at least `13 > 4 ≥ 2^n`. -/
theorem two_pow_ne_three_term_three_pow_sum {a b c n : ℕ}
    (h1 : c < b) (h2 : b < a) :
    2 ^ n ≠ 3 ^ a + 3 ^ b + 3 ^ c := by
  intro h
  have hc_zero : c = 0 := by
    by_contra hc
    apply three_not_dvd_two_pow' n
    rw [h]
    have ha_ne : a ≠ 0 := by omega
    have hb_ne : b ≠ 0 := by omega
    exact dvd_add (dvd_add (dvd_pow_self 3 ha_ne) (dvd_pow_self 3 hb_ne))
                  (dvd_pow_self 3 hc)
  subst hc_zero
  rw [pow_zero] at h
  have hb_pos : 1 ≤ b := by omega
  have ha_ge : 2 ≤ a := by omega
  rcases Nat.lt_or_ge n 3 with hn | hn
  · -- n < 3: RHS ≥ 13 > 4 ≥ 2^n
    have h3a : (3 : ℕ) ^ 2 ≤ 3 ^ a := Nat.pow_le_pow_right (by decide) ha_ge
    have h3b : (3 : ℕ) ^ 1 ≤ 3 ^ b := Nat.pow_le_pow_right (by decide) hb_pos
    simp at h3a h3b
    interval_cases n <;> simp at h <;> omega
  · -- n ≥ 3: 2^n ≡ 0 (mod 8) but RHS mod 8 ∈ {3, 5, 7}.
    have h8 : 2 ^ n % 8 = 0 := by
      have hdvd : (8 : ℕ) ∣ 2 ^ n := by
        rw [show (8 : ℕ) = 2 ^ 3 from by norm_num]
        exact pow_dvd_pow 2 hn
      omega
    have ha8 : (3 : ℕ) ^ a % 8 = 1 ∨ (3 : ℕ) ^ a % 8 = 3 := by
      rw [three_pow_mod_eight]; split_ifs <;> [left; right] <;> rfl
    have hb8 : (3 : ℕ) ^ b % 8 = 1 ∨ (3 : ℕ) ^ b % 8 = 3 := by
      rw [three_pow_mod_eight]; split_ifs <;> [left; right] <;> rfl
    have h_rhs_mod : (3 ^ a + 3 ^ b + 1 : ℕ) % 8 ≠ 0 := by
      rcases ha8 with ha8 | ha8 <;> rcases hb8 with hb8 | hb8 <;>
        (rw [Nat.add_mod, Nat.add_mod (3 ^ a) (3 ^ b), ha8, hb8]; decide)
    rw [h] at h8
    exact h_rhs_mod h8

/-! ## Catalogue summary

The known Erdős exceptions match the term-count theorems perfectly:

* `k = 1`, unique witness `(n, a) = (0, 0)`: `2^0 = 3^0`.  Matches `N = 0`.
* `k = 2`, unique witness `(n, a, b) = (2, 1, 0)`: `2^2 = 3 + 1`.
  Matches `N = 2`.
* `k = 3`, **no witness** (proved above).
* `k = 4`, ?  Should have unique witness `(n, a, b, c, d) = (8, 5, 2, 1, 0)`:
  `2^8 = 243 + 9 + 3 + 1`.  Matches `N = 8`.  Open in Lean.
* `k ≥ 5`, ?  Should have no witnesses (Erdős says no more exceptions).
  Open in Lean. -/

end Collatz.Erdos
