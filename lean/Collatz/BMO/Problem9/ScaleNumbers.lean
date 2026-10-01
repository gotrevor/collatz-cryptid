/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Exponential

/-!
# BMO #9, port of Rocq `Module ScaleNumbers` (BMO9.v lines 3356-3483, ccz181078)

Numeric facts about the subscale `m = 2^20 + 32x`.  The scale `x` is used as an exponent,
hence `x : ℕ`; Rocq `Z.log2_up` is `Nat.clog 2` and `Z.log2` is `Nat.log 2`.  Pure size
statements about naturals are stated in `ℕ`; the budget/output inequalities in `ℤ`.
-/

namespace BMO9.ScaleNumbers

theorem threshold (x : ℕ) (hx : 121 ≤ x) : (2:ℤ)^20 + 32*x < 2^(x-1) := by
  have := Exponential.final_square x (by omega)
  have hx' : (121:ℤ) ≤ x := by exact_mod_cast hx
  nlinarith

theorem threshold_nat (x : ℕ) (hx : 121 ≤ x) : 2^20 + 32*x ≤ 2^x := by
  have h := threshold x hx
  have h2 : (2:ℤ)^(x-1) ≤ 2^x := pow_le_pow_right₀ (by norm_num) (by omega)
  have : ((2^20 + 32*x : ℕ):ℤ) ≤ ((2^x : ℕ):ℤ) := by push_cast; linarith
  exact_mod_cast this

theorem subscale (x : ℕ) (hx : 121 ≤ x) :
    20 ≤ Nat.clog 2 (2^20 + 32*x) ∧ Nat.clog 2 (2^20 + 32*x) ≤ x ∧
    (2:ℤ)^20 + 32*x ≤ 2^14*x ∧ (x:ℤ) ≤ (2^20 + 32*x)^2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Nat.clog_mono_right 2 (show 2^20 ≤ 2^20 + 32*x by omega)
    rwa [Nat.clog_pow 2 20 (by norm_num)] at this
  · exact Nat.clog_le_of_le_pow (threshold_nat x hx)
  · have hx' : (121:ℤ) ≤ x := by exact_mod_cast hx
    norm_num; linarith
  · have hx' : (0:ℤ) ≤ x := by positivity
    nlinarith

theorem small_window (x : ℕ) (hx : x ≤ 2^20) : Nat.clog 2 (2^20 + 32*x) ≤ 26 :=
  Nat.clog_le_of_le_pow (by norm_num at hx ⊢; omega)

theorem large_window (x : ℕ) (hx : 2^20 < x) :
    20 ≤ Nat.log 2 x ∧ 2^Nat.log 2 x ≤ x ∧ x < 2^(Nat.log 2 x + 1) ∧
    Nat.clog 2 (2^20 + 32*x) ≤ Nat.log 2 x + 7 ∧ 2^20 + 32*x ≤ 64*x := by
  have hx0 : x ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hx0
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
  have hn : 20 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) hx.le
  refine ⟨hn, hlo, hhi, ?_, by omega⟩
  apply Nat.clog_le_of_le_pow
  rw [Table_pow_split_nat]
  omega
where
  Table_pow_split_nat : 2^(Nat.log 2 x + 7) = 64*2^(Nat.log 2 x + 1) := by
    rw [show Nat.log 2 x + 7 = 6 + (Nat.log 2 x + 1) by omega, pow_add]; norm_num

theorem huge_window (x : ℕ) (hm : 2^120 < 2^20 + 32*x) : 2^114 < x ∧ 114 ≤ Nat.log 2 x := by
  have hx : 2^114 < x := by norm_num at hm ⊢; omega
  exact ⟨hx, Nat.le_log_of_pow_le (by norm_num) hx.le⟩

theorem small_budget_poly (y n : ℤ) (hy0 : 0 ≤ y) (hy : y ≤ n+7) (hn : 0 ≤ n) :
    27 + 2*(30*y)*(6*y+9) + 30*y ≤ 1024*(n+8)^2 := by
  nlinarith

theorem small_budget (x : ℕ) (hx : 121 ≤ x) :
    let y : ℤ := Nat.clog 2 (2^20 + 32*x)
    15*(x:ℤ) + 27 + 2*(30*y)*(6*y+9) + 30*y ≤ 2^20 + 32*x + 1 := by
  intro y
  have hy0 : 0 ≤ y := by positivity
  rcases le_or_gt x (2^20) with hs | hl
  · have h26 : y ≤ 26 := by
      have := small_window x hs; simp only [y]; exact_mod_cast this
    have := small_budget_poly y 19 hy0 (by linarith) (by norm_num)
    have hx' : (121:ℤ) ≤ x := by exact_mod_cast hx
    nlinarith
  · obtain ⟨hn, hpow, -, hyn, -⟩ := large_window x hl
    have hyn' : y ≤ (Nat.log 2 x : ℤ) + 7 := by simp only [y]; exact_mod_cast hyn
    have hpoly := small_budget_poly y (Nat.log 2 x) hy0 hyn' (by positivity)
    have ht := Exponential.square_tail (Nat.log 2 x) hn
    have hpow' : (2:ℤ)^Nat.log 2 x ≤ x := by exact_mod_cast hpow
    linarith

theorem large_budget_poly (y : ℤ) (hy : 0 ≤ y) :
    27 + 2*(2^64*(y+1)^4)*(6*y+9) + 2^64*(y+1)^4 ≤ 2^70*(y+1)^5 := by
  have HP : 1 ≤ (y+1)^4 := one_le_pow₀ (by linarith)
  rw [show (y+1)^5 = (y+1)^4*(y+1) by ring]
  generalize (y+1)^4 = z at HP ⊢
  nlinarith

theorem large_budget (x : ℕ) (_hx : 121 ≤ x) (hm : 2^120 < 2^20 + 32*x) :
    let y : ℤ := Nat.clog 2 (2^20 + 32*x)
    15*(x:ℤ) + 27 + 2*(2^64*(y+1)^4)*(6*y+9) + 2^64*(y+1)^4 ≤ 2^20 + 32*x + 1 := by
  intro y
  obtain ⟨hxl, hn⟩ := huge_window x hm
  have h20 : 2^20 < x := lt_trans (by norm_num) hxl
  obtain ⟨-, hpow, -, hyn, -⟩ := large_window x h20
  have hy0 : 0 ≤ y := by positivity
  have hyn' : y ≤ (Nat.log 2 x : ℤ) + 7 := by simp only [y]; exact_mod_cast hyn
  have hpoly := large_budget_poly y hy0
  have hmono : (y+1)^5 ≤ ((Nat.log 2 x : ℤ)+8)^5 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 5
  have ht := Exponential.fifth_tail (Nat.log 2 x) hn
  have hpow' : (2:ℤ)^Nat.log 2 x ≤ x := by exact_mod_cast hpow
  nlinarith

theorem product_squares (a A b B : ℤ) (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B) :
    64*a^2*b^2 ≤ 64*A^2*B^2 := by
  have h1 : a^2 ≤ A^2 := pow_le_pow_left₀ ha haA 2
  have h2 : b^2 ≤ B^2 := pow_le_pow_left₀ hb hbB 2
  have := mul_le_mul h1 h2 (by positivity) (by positivity)
  nlinarith

theorem small_output (x y m : ℤ) (hx : 121 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ x) (hm0 : 0 ≤ m)
    (hm : m ≤ 2^14*x) : 64*(30*y+1)^2*m^2 ≤ 2^64*(x+1)^4 := by
  have H := product_squares (30*y+1) (32*x) m (2^14*x) (by linarith) (by linarith) hm0 hm
  rw [show 64*(32*x)^2*(2^14*x)^2 = 2^44*x^4 by ring] at H
  have h4 : x^4 ≤ (x+1)^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have : (0:ℤ) ≤ x^4 := by positivity
  nlinarith

theorem large_output (x y m : ℤ) (n : ℕ) (hx : 1 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ n+7)
    (hn : 114 ≤ n) (hnx : 2^n ≤ x) (hm0 : 0 ≤ m) (hm : m ≤ 64*x) :
    64*(2^64*(y+1)^4+1)^2*m^2 ≤ 2^64*(x+1)^4 := by
  have HP : 1 ≤ (y+1)^4 := one_le_pow₀ (by linarith)
  have H := product_squares (2^64*(y+1)^4+1) (2^65*(y+1)^4) m (64*x) (by positivity)
    (by nlinarith) hm0 hm
  rw [show 64*(2^65*(y+1)^4)^2*(64*x)^2 = 2^148*(y+1)^8*x^2 by ring] at H
  have hy8 : (y+1)^8 ≤ ((n:ℤ)+8)^8 := pow_le_pow_left₀ (by linarith) (by linarith) 8
  have ht := Exponential.eighth_tail n hn
  have hn2 : (2:ℤ)^(2*n) ≤ x^2 := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hnx 2
  have H8 : 2^84*(y+1)^8 ≤ x^2 := by nlinarith
  have hstep : 2^148*(y+1)^8*x^2 ≤ 2^64*x^4 := by
    have := mul_le_mul_of_nonneg_right H8 (by positivity : (0:ℤ) ≤ 2^64*x^2)
    nlinarith
  have h4 : x^4 ≤ (x+1)^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  linarith

end BMO9.ScaleNumbers
