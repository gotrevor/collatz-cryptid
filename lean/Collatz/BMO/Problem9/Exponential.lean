/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic

/-!
# BMO #9, port of Rocq `Module Exponential` (BMO9.v lines 3199-3272, ccz181078)

Polynomial-versus-exponential tail estimates.  Rocq exponents (`p`, `slope`, `start`, `n`)
are `ℕ` here; the inequalities themselves live in `ℤ`.
-/

namespace BMO9.Exponential

/-- A ratio estimate at a single base controls every larger argument. -/
theorem power_ratio (a b c : ℤ) (p : ℕ) (hb : 0 < b) (hab : b ≤ a) (_hc : 0 ≤ c)
    (hbase : (b+1)^p ≤ c*b^p) : (a+1)^p ≤ c*a^p := by
  have H : (b*(a+1))^p ≤ ((b+1)*a)^p :=
    pow_le_pow_left₀ (by nlinarith) (by nlinarith) p
  rw [mul_pow, mul_pow] at H
  have h1 : 0 ≤ a^p := pow_nonneg (by omega) p
  have h2 : 0 < b^p := by positivity
  have h3 := mul_le_mul_of_nonneg_right hbase h1
  have h4 : b^p*(a+1)^p ≤ b^p*(c*a^p) := by nlinarith
  exact le_of_mul_le_mul_left h4 h2

theorem shifted_power (K c : ℤ) (p start slope : ℕ) (hK : 0 ≤ K) (hstart : 0 < (start:ℤ)+c)
    (hratio : ((start:ℤ)+c+1)^p ≤ 2^slope*(start+c)^p)
    (hbase : K*((start:ℤ)+c)^p < 2^(slope*start)) :
    ∀ n : ℕ, start ≤ n → K*((n:ℤ)+c)^p < 2^(slope*n) := by
  have H : ∀ i : ℕ, K*(((start+i : ℕ):ℤ)+c)^p < 2^(slope*(start+i)) := by
    intro i
    induction i with
    | zero => simpa using hbase
    | succ i ih =>
      have hstep := power_ratio (((start+i:ℕ):ℤ)+c) ((start:ℤ)+c) (2^slope) p hstart
        (by push_cast; omega) (by positivity) hratio
      have e1 : (((start+(i+1) : ℕ):ℤ)+c) = (((start+i:ℕ):ℤ)+c)+1 := by push_cast; ring
      have e2 : slope*(start+(i+1)) = slope*(start+i) + slope := by ring
      rw [e1, e2, pow_add]
      have hp : (0:ℤ) < 2^slope := by positivity
      have := mul_le_mul_of_nonneg_left hstep hK
      have := mul_lt_mul_of_pos_left ih hp
      nlinarith
  intro n hn
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact H i

theorem square_tail (n : ℕ) (hn : 20 ≤ n) : 1024*((n:ℤ)+8)^2 < 2^n := by
  have := shifted_power 1024 8 2 20 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) n hn
  simpa using this

theorem fifth_tail (n : ℕ) (hn : 114 ≤ n) : 2^70*((n:ℤ)+8)^5 < 2^n := by
  have := shifted_power (2^70) 8 5 114 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) n hn
  simpa using this

theorem eighth_tail (n : ℕ) (hn : 114 ≤ n) : 2^84*((n:ℤ)+8)^8 < 2^(2*n) :=
  shifted_power (2^84) 8 8 114 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) n hn

theorem final_tail (n : ℕ) (hn : 1024 ≤ n) : 2^70*((n:ℤ)+1)^5 < 2^(n-1) := by
  have H := shifted_power (2^71) 1 5 1024 1 (by norm_num) (by norm_num) (by norm_num)
    (by
      have h1 : (2:ℤ)^71*((1024:ℕ)+1)^5 < 2^126 := by norm_num
      have h2 : (2:ℤ)^126 ≤ 2^(1*1024) := pow_le_pow_right₀ (by norm_num) (by norm_num)
      exact lt_of_lt_of_le h1 h2) n hn
  have e : (2:ℤ)^n = 2*2^(n-1) := by rw [← pow_succ']; congr 1; omega
  rw [one_mul, e] at H
  have : (2:ℤ)^71 = 2*2^70 := by norm_num
  rw [this] at H
  nlinarith

theorem final_square (n : ℕ) (hn : 17 ≤ n) : 200*(n:ℤ)^2 < 2^(n-1) := by
  have H := shifted_power 400 0 2 17 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) n hn
  have e : (2:ℤ)^n = 2*2^(n-1) := by rw [← pow_succ']; congr 1; omega
  rw [one_mul, e, add_zero] at H
  nlinarith

end BMO9.Exponential
