/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.SmallScale

/-!
# BMO #9, port of Rocq `Module LargeStep` (BMO9.v lines 3273-3355, ccz181078)

One multiscale lift from a subscale `m` to `L ≤ 2^x`.  Levels, exponents and the bound `r`
are `ℕ`; the arithmetic hypotheses are stated in `ℤ`.
-/

namespace BMO9.LargeStep

open Table WordLibrary WordBlocks Multiscale

theorem mass_bound (L m x r : ℕ) (hx : 3 ≤ x) (hm : m ≤ L) (hL : L ≤ 2^x) :
    0 ≤ 12*(L:ℤ)^3 + 3 + r*(12*(m:ℤ)^3 + 3) ∧
      12*(L:ℤ)^3 + 3 + r*(12*(m:ℤ)^3 + 3) ≤ 13*(r+1)*2^(3*x) := by
  have HmL : (m:ℤ)^3 ≤ (L:ℤ)^3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hm) 3
  have HLP : (L:ℤ)^3 ≤ (2^x)^3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL) 3
  have HP : (2:ℤ)^3 ≤ 2^(3*x) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [SmallScale.exp3] at HP ⊢
  have : (0:ℤ) ≤ (m:ℤ)^3 := by positivity
  have hr : (0:ℤ) ≤ r := by positivity
  norm_num at HP
  constructor
  · positivity
  · nlinarith

theorem budget (m x y r : ℕ) (M : ℤ) (_hx : 3 ≤ x) (hM0 : 0 ≤ M)
    (hM : M ≤ 13*(r+1)*2^(3*x)) (hbudget : 15*x + 27 + 2*r*(6*y+9) + r ≤ m + 1) :
    2^(2*(6*x+9+r*(6*y+9)))*(12*M+8) < (2:ℤ)^(m+1) := by
  have Hrpow : ((r+1:ℕ):ℤ) < 2^(r+1) := by exact_mod_cast Nat.lt_two_pow_self
  push_cast at Hrpow
  have HP : (0:ℤ) < 2^(3*x) := by positivity
  have HE : (2:ℤ)^(3*x+8+(r+1)) = 256*2^(3*x)*2^(r+1) := by rw [pow_add, pow_add]; ring
  have HMpow : 12*M + 8 < (2:ℤ)^(3*x+8+(r+1)) := by
    rw [HE]
    have : (0:ℤ) ≤ r := by positivity
    nlinarith
  have Hstep : 2^(2*(6*x+9+r*(6*y+9)))*(12*M+8) < (2:ℤ)^(15*x+27+2*r*(6*y+9)+r) := by
    rw [show 15*x+27+2*r*(6*y+9)+r = 2*(6*x+9+r*(6*y+9)) + (3*x+8+(r+1)) by ring, pow_add]
    exact mul_lt_mul_of_pos_left HMpow (by positivity)
  exact Hstep.trans_le (pow_le_pow_right₀ (by norm_num) hbudget)

theorem contraction_time (x r : ℕ) (M : ℤ) (hx : 3 ≤ x) (hrpow : r + 1 ≤ 2^x) (hM0 : 0 ≤ M)
    (hM : M ≤ 13*(r+1)*2^(3*x)) : 2*M + 2 ≤ (3:ℤ)^(4*x) := by
  have hr : ((r:ℤ) + 1) ≤ 2^x := by exact_mod_cast hrpow
  have HE : (2:ℤ)^(4*x) = 2^x*2^(3*x) := by rw [← pow_add]; ring_nf
  have p1 : (0:ℤ) < 2^x := by positivity
  have p3 : (0:ℤ) < 2^(3*x) := by positivity
  have HMpow : 2*M + 2 ≤ 28*(2:ℤ)^(4*x) := by rw [HE]; nlinarith
  have Hdom : 28*(2:ℤ)^(4*x) ≤ 3^(4*x) := by
    rw [pow_mul, pow_mul]; norm_num
    have H64 : (64:ℤ)^x ≤ 81^x := pow_le_pow_left₀ (by norm_num) (by norm_num) x
    rw [show (64:ℤ) = 4*16 by norm_num, mul_pow] at H64
    have H4 : (64:ℤ) ≤ 4^x := by
      calc (64:ℤ) = 4^3 := by norm_num
        _ ≤ 4^x := pow_le_pow_right₀ (by norm_num) hx
    have : (0:ℤ) < 16^x := by positivity
    nlinarith
  linarith

theorem length_estimate (r x m : ℤ) (hr : 1 ≤ r) (hm : 2 ≤ m) (hx : x ≤ m^2) :
    (r+1)*(4*x + 13*r*m^2 + 2) + r ≤ 64*(r+1)^2*m^2 := by
  have := mul_le_mul_of_nonneg_left (show 4*x + 13*r*m^2 + 2 ≤ 4*m^2 + 13*r*m^2 + 2 by linarith)
    (show (0:ℤ) ≤ r+1 by linarith)
  have hM : (4:ℤ) ≤ m^2 := by nlinarith
  have hr0 : (0:ℤ) ≤ r := by linarith
  nlinarith [mul_nonneg (mul_nonneg hr0 hr0) (show (0:ℤ) ≤ m^2 by positivity),
    mul_nonneg hr0 (show (0:ℤ) ≤ m^2 by positivity)]

theorem lift (m L x y r : ℕ) (hx : 3 ≤ x) (hm : 2 ≤ m) (hmL : m ≤ L) (hr : 1 ≤ r)
    (hL : L ≤ 2^x) (hsquare : (x:ℤ) ≤ (m:ℤ)^2)
    (hparams : Parameters L (6*x+9) (12*(L:ℤ)^3 + 3))
    (hlow : Parameters m (6*y+9) (12*(m:ℤ)^3 + 3)) (hbound : WordLink.Bound m r)
    (hbudget : 15*(x:ℤ) + 27 + 2*r*(6*y+9) + r ≤ m + 1) :
    WordLink.Bound L (64*((r:ℤ)+1)^2*(m:ℤ)^2) := by
  obtain ⟨HM0, HM⟩ := mass_bound L m x r hx hmL hL
  have hbudget' : 15*x + 27 + 2*r*(6*y+9) + r ≤ m + 1 := by exact_mod_cast hbudget
  have hexp := budget m x y r _ hx HM0 HM hbudget'
  have hrpow : r + 1 ≤ 2^x := by
    have : 18*r ≤ 2*r*(6*y+9) := by nlinarith
    omega
  have htime := contraction_time x r _ hx hrpow HM0 HM
  have hm3 : (8:ℤ) ≤ (m:ℤ)^3 := by
    have : (2:ℤ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hq : (r:ℤ)*(12*(m:ℤ)^3 + 3) + 4 ≤ ((13*r*m^2 : ℕ):ℤ)*(m:ℤ) := by
    push_cast
    have : (1:ℤ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hlift := lift_bound m L r (6*x+9) (6*y+9) (12*(L:ℤ)^3+3) (12*(m:ℤ)^3+3) (4*x)
    (13*r*m^2) (by omega) (by positivity) (by positivity) hparams hlow hbound
    (by convert hexp using 3) (by convert htime using 1) hq
  refine WordLink.bound_mono L L _ _ le_rfl ?_ hlift
  push_cast
  exact length_estimate r x m (by exact_mod_cast hr) (by exact_mod_cast hm) hsquare

end BMO9.LargeStep
