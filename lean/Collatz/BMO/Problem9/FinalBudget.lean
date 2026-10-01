/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.GlobalBounds

/-!
# BMO #9, port of Rocq `Module FinalBudget` (BMO9.v lines 3552-3650, ccz181078)

The budget `Closure.Budget k` for every level `k > 65536` whose predecessors are good, using
the word level `L = 8·⌈log₂ k⌉`.
-/

namespace BMO9.FinalBudget

open Table

theorem cutoff (k : ℕ) (hk : 65536 < k) :
    17 ≤ CheckTable.log2up k ∧ 2^(CheckTable.log2up k - 1) < k ∧ k ≤ 2^CheckTable.log2up k ∧
    2 ≤ 8*CheckTable.log2up k ∧ 8*CheckTable.log2up k < k ∧
    CheckTable.log2up (8*CheckTable.log2up k) ≤ CheckTable.log2up k := by
  set x := CheckTable.log2up k
  have hkx : k ≤ 2^x := Nat.le_pow_clog (by norm_num) k
  have hx : 17 ≤ x := by
    by_contra h; push Not at h
    have : 2^x ≤ 2^16 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlow : 2^(x-1) < k := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hsq := Exponential.final_square x hx
  have hlowZ : ((2^(x-1) : ℕ) : ℤ) < k := by exact_mod_cast hlow
  push_cast at hlowZ
  have hx' : (17:ℤ) ≤ x := by exact_mod_cast hx
  have h8 : 8*x < k := by
    have : ((8*x : ℕ) : ℤ) < k := by push_cast; nlinarith
    exact_mod_cast this
  have h8' : 8*x ≤ 2^x := by
    have h2 : (2:ℤ)^(x-1) ≤ 2^x := pow_le_pow_right₀ (by norm_num) (by omega)
    have : ((8*x : ℕ) : ℤ) ≤ ((2^x : ℕ) : ℤ) := by push_cast; nlinarith
    exact_mod_cast this
  exact ⟨hx, hlow, hkx, by omega, h8, Nat.clog_le_of_le_pow h8'⟩

theorem small_depth (x y : ℤ) (hx : 17 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ x) :
    6*x + 9 + (30*y+1)*(6*y+9) + 8*x ≤ 200*x^2 := by nlinarith

theorem large_depth_poly (x : ℤ) (hx : 0 ≤ x) :
    6*x + 9 + (2^64*(x+1)^4+1)*(6*x+9) + 8*x ≤ 2^70*(x+1)^5 := by
  have HP : 1 ≤ (x+1)^4 := one_le_pow₀ (by linarith)
  rw [show (x+1)^5 = (x+1)^4*(x+1) by ring]
  generalize (x+1)^4 = z at HP ⊢
  nlinarith

theorem large_depth (x y : ℤ) (hy0 : 0 ≤ y) (hy : y ≤ x) :
    6*x + 9 + (2^64*(y+1)^4+1)*(6*y+9) + 8*x ≤ 2^70*(x+1)^5 := by
  have HP : (y+1)^4 ≤ (x+1)^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have HP0 : 0 ≤ (y+1)^4 := by positivity
  have Hprod := mul_le_mul (show 2^64*(y+1)^4+1 ≤ 2^64*(x+1)^4+1 by linarith)
    (show 6*y+9 ≤ 6*x+9 by linarith) (by linarith) (by positivity)
  have := large_depth_poly x (by linarith)
  linarith

theorem mass_poly (k : ℤ) (hk : 3 ≤ k) : 2*(12*k^3 + k*(12*k^3+3)) + 3 < k^8 := by
  have hk3 : (27:ℤ) ≤ k^3 := by
    calc (27:ℤ) = 3^3 := by norm_num
      _ ≤ k^3 := pow_le_pow_left₀ (by norm_num) hk 3
  have h4 : 3*k^3 ≤ k^4 := by
    rw [show k^4 = k*k^3 by ring]; nlinarith
  have Hsmall : 2*(12*k^3 + k*(12*k^3+3)) + 3 ≤ 40*k^4 := by
    rw [show k*(12*k^3+3) = 12*k^4 + 3*k by ring]; nlinarith
  have Hpow : 81 ≤ k^4 := by
    calc (81:ℤ) = 3^4 := by norm_num
      _ ≤ k^4 := pow_le_pow_left₀ (by norm_num) hk 4
  have Hbig : 40*k^4 < k^8 := by
    rw [show k^8 = k^4*k^4 by ring]
    generalize k^4 = z at Hpow ⊢
    nlinarith
  linarith

theorem mass_bound (k L n : ℤ) (hk : 3 ≤ k) (hL0 : 0 ≤ L) (hL : L ≤ k) (_hn0 : 0 ≤ n)
    (hn : n ≤ k) : 2*(12*k^3 + n*(12*L^3+3)) + 3 < k^8 := by
  have h1 : L^3 ≤ k^3 := pow_le_pow_left₀ hL0 hL 3
  have h2 : 0 ≤ L^3 := by positivity
  have h3 := mul_le_mul hn (show 12*L^3+3 ≤ 12*k^3+3 by linarith) (by linarith) (by linarith)
  have := mass_poly k hk
  linarith

theorem assemble (k r : ℕ) (hk : 65536 < k)
    (hword : WordLink.Bound (8*CheckTable.log2up k) r)
    (HD : 6*(CheckTable.log2up k : ℤ) + 9 + ((r:ℤ)+1)*(6*(CheckTable.log2up
      (8*CheckTable.log2up k) : ℤ) + 9) + 8*(CheckTable.log2up k : ℤ) < k) :
    Closure.Budget k := by
  obtain ⟨hx17, hlow, hkx, hL2, hLk, hys⟩ := cutoff k hk
  set x := CheckTable.log2up k
  have hy0 : (0:ℤ) ≤ CheckTable.log2up (8*x) := by positivity
  have hn : (r:ℤ) + 1 < k := by
    have : (0:ℤ) ≤ x := by positivity
    nlinarith
  refine ⟨8*x, r+1, by omega, hLk, by push_cast; simpa using hword, by push_cast; linarith, ?_⟩
  have hkZ : (65536:ℤ) < k := by exact_mod_cast hk
  have := mass_bound k (8*x : ℕ) (r+1 : ℕ) (by linarith) (by positivity)
    (by exact_mod_cast hLk.le) (by positivity) (by push_cast; linarith)
  have hk8 : (k:ℤ)^8 ≤ 2^(8*x) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hkx) 8
  push_cast at this ⊢
  linarith

theorem budget (k : ℕ) (hk : 65536 < k) (hprev : Closure.Earlier k) : Closure.Budget k := by
  obtain ⟨hx, hlow, hkx, hL2, hLk, hys⟩ := cutoff k hk
  set x := CheckTable.log2up k
  set y := CheckTable.log2up (8*x)
  have hlowZ : ((2^(x-1) : ℕ) : ℤ) < k := by exact_mod_cast hlow
  push_cast at hlowZ
  have hyx : (y:ℤ) ≤ x := by exact_mod_cast hys
  have hx' : (17:ℤ) ≤ x := by exact_mod_cast hx
  by_cases hsmall : 8*x ≤ 2^120
  · refine assemble k (30*y) hk ?_ ?_
    · have := SmallScale.range120 (8*x) hL2 hsmall
        (SmallScale.earlier_parameters k (8*x) (by omega) hLk hprev)
      push_cast; exact this
    · have := small_depth x y hx' (by positivity) hyx
      have := Exponential.final_square x hx
      push_cast; nlinarith
  · push Not at hsmall
    refine assemble k (2^64*(y+1)^4) hk ?_ ?_
    · have := GlobalBounds.quartic k hprev (8*x) hL2 hLk
      push_cast; exact this
    · have hx1024 : 1024 ≤ x := by
        have : 8*1024 < 2^120 := by norm_num
        omega
      have := large_depth x y (by positivity) hyx
      have := Exponential.final_tail x hx1024
      push_cast; nlinarith

end BMO9.FinalBudget
