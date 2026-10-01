/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Multiscale
import Collatz.BMO.Problem9.Closure

/-!
# BMO #9, port of Rocq `Module SmallScale` (BMO9.v lines 3120-3198, ccz181078)

Word-length bounds `30·⌈log₂ L⌉` for every level `L ≤ 2^120`, lifted from the finite base
`Bound 2048 6`.  Rocq `Z.log2_up` is `Nat.clog 2` (`CheckTable.log2up`).
-/

namespace BMO9.SmallScale

open Table WordLibrary WordBlocks Multiscale

theorem base_parameters : Parameters 2048 5 5472 :=
  fun k hk hL ↦ WordCheck.kernel_bounds k hk hL

theorem earlier_parameters (k L : ℕ) (hL1 : 1 ≤ L) (hL : L < k) (hprev : Closure.Earlier k) :
    Parameters L (6*CheckTable.log2up L + 9) (12*(L:ℤ)^3 + 3) := by
  intro z hz hindex
  obtain ⟨e, hb, hs, -⟩ := hz
  obtain ⟨hd, hg⟩ := Closure.kernel_bounds k L hL1 hL hprev z.index z.pair e hs hindex hb
  exact ⟨by simp only [depth]; exact_mod_cast hd, hg⟩

theorem exp3 (x : ℕ) : (2:ℤ)^(3*x) = (2^x)^3 := by rw [mul_comm, pow_mul]

theorem mass_bound (L x : ℕ) (hL : 2048 < L) (hx : 12 ≤ x) (hpow : L ≤ 2^x) :
    12*(L:ℤ)^3 + 3 + 6*5472 ≤ 13*2^(3*x) := by
  have h1 : (L:ℤ)^3 ≤ (2^x)^3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpow) 3
  have h2 : (2:ℤ)^16 ≤ 2^(3*x) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [exp3] at h2 ⊢
  norm_num at h2
  linarith

theorem budget120 (x : ℕ) (M : ℤ) (hx : 12 ≤ x) (hx' : x ≤ 120) (_hM0 : 0 ≤ M)
    (hM : M ≤ 13*2^(3*x)) : 2^(2*(6*x+39))*(12*M+8) < (2:ℤ)^2049 := by
  have HP : (0:ℤ) < 2^(3*x) := by positivity
  have HB : 12*M + 8 < (2:ℤ)^(3*x+8) := by rw [pow_add]; norm_num; nlinarith
  have Hbig : 2^(2*(6*x+39))*(12*M+8) < (2:ℤ)^(15*x+86) := by
    rw [show 15*x+86 = 2*(6*x+39) + (3*x+8) by ring, pow_add]
    exact mul_lt_mul_of_pos_left HB (by positivity)
  exact Hbig.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))

theorem contraction_time (x : ℕ) (M : ℤ) (_hM0 : 0 ≤ M) (hM : M ≤ 13*2^(3*x)) :
    2*M + 2 ≤ (3:ℤ)^(2*x+4) := by
  have H89 : (8:ℤ)^x ≤ 9^x := pow_le_pow_left₀ (by norm_num) (by norm_num) x
  have H1 : (1:ℤ) ≤ 8^x := one_le_pow₀ (by norm_num)
  rw [pow_add, pow_mul]
  rw [pow_mul] at hM
  norm_num at hM ⊢
  nlinarith

theorem range120 (L : ℕ) (hL2 : 2 ≤ L) (hL : L ≤ 2^120)
    (hparams : Parameters L (6*CheckTable.log2up L + 9) (12*(L:ℤ)^3 + 3)) :
    WordLink.Bound L (30*(CheckTable.log2up L : ℤ)) := by
  by_cases hsmall : L ≤ 2048
  · have h1 : 1 ≤ CheckTable.log2up L := by
      unfold CheckTable.log2up
      by_contra h; push Not at h
      have := Nat.le_pow_clog (by norm_num : 1 < 2) L
      interval_cases (Nat.clog 2 L); simp at this; omega
    exact WordLink.bound_mono 2048 L 6 _ hsmall (by omega) WordLink.base_bound
  · set x := CheckTable.log2up L with hxdef
    have HLpow : L ≤ 2^x := Nat.le_pow_clog (by norm_num) L
    have hx12 : 12 ≤ x := by
      by_contra h; push Not at h
      have : 2^x ≤ 2^11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hx120 : x ≤ 120 := Nat.clog_le_of_le_pow hL
    have HM := mass_bound L x (by omega) hx12 HLpow
    have hL3 : (0:ℤ) ≤ (L:ℤ)^3 := by positivity
    have hlift := lift_bound 2048 L 6 (6*x+9) 5 (12*(L:ℤ)^3+3) 5472 (2*x+4) 17 (by norm_num)
      (by norm_num) (by positivity) hparams base_parameters WordLink.base_bound
      (by
        have := budget120 x (12*(L:ℤ)^3+3+6*5472) hx12 hx120 (by positivity) HM
        rw [show 6*x+9+6*5 = 6*x+39 by ring]
        push_cast; linarith)
      (by
        have := contraction_time x (12*(L:ℤ)^3+3+6*5472) (by positivity) HM
        push_cast; linarith)
      (by norm_num)
    exact WordLink.bound_mono L L _ _ le_rfl (by push_cast; omega) hlift

end BMO9.SmallScale
