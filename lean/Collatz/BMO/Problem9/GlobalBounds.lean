/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.LargeStep
import Collatz.BMO.Problem9.ScaleNumbers

/-!
# BMO #9, port of Rocq `Module GlobalBounds` (BMO9.v lines 3484-3551, ccz181078)

The quartic word-length bound `2^64·(⌈log₂ L⌉+1)^4` for every level `2 ≤ L < k`, by strong
induction on `L` through the subscale `m = 2^20 + 32·⌈log₂ L⌉`.
-/

namespace BMO9.GlobalBounds

open Table WordLibrary Multiscale

theorem linear_quartic (x : ℤ) (hx : 0 ≤ x) : 30*x ≤ 2^64*(x+1)^4 := by
  have : x + 1 ≤ (x+1)^4 := by
    calc x + 1 = (x+1)^1 := by ring
      _ ≤ (x+1)^4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

theorem induction_step (k L : ℕ) (hprev : Closure.Earlier k) (hL2 : 2 ≤ L) (hLk : L < k)
    (IH : ∀ m, 2 ≤ m → m < L →
      WordLink.Bound m (2^64*((CheckTable.log2up m : ℤ)+1)^4)) :
    WordLink.Bound L (2^64*((CheckTable.log2up L : ℤ)+1)^4) := by
  have hparams := SmallScale.earlier_parameters k L (by omega) hLk hprev
  by_cases hsmall : L ≤ 2^120
  · exact WordLink.bound_mono L L _ _ le_rfl (linear_quartic _ (by positivity))
      (SmallScale.range120 L hL2 hsmall hparams)
  · set x := CheckTable.log2up L with hxdef
    have hLx : L ≤ 2^x := Nat.le_pow_clog (by norm_num) L
    have hx : 121 ≤ x := by
      by_contra h; push Not at h
      have : 2^x ≤ 2^120 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hlow : 2^(x-1) < L := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    set m := 2^20 + 32*x with hmdef
    set y := CheckTable.log2up m with hydef
    have hmL : m < L := by
      have h1 := ScaleNumbers.threshold x hx
      have h2 : ((2^(x-1) : ℕ) : ℤ) < L := by exact_mod_cast hlow
      have : (m:ℤ) < L := by push_cast at h2 ⊢; linarith
      exact_mod_cast this
    obtain ⟨hy20, hyx, hm14, hxm⟩ := ScaleNumbers.subscale x hx
    have hmZ : (m:ℤ) = 2^20 + 32*(x:ℤ) := by simp [hmdef]
    have hyZ : ((Nat.clog 2 (2^20 + 32*x) : ℕ) : ℤ) = (y:ℤ) := rfl
    have hmparams := SmallScale.earlier_parameters k m (by omega) (by omega) hprev
    by_cases hmsmall : m ≤ 2^120
    · have hword := SmallScale.range120 m (by omega) hmsmall hmparams
      have hb := ScaleNumbers.small_budget x hx
      simp only at hb
      have hlift := LargeStep.lift m L x y (30*y) (by omega) (by omega) hmL.le (by omega) hLx
        (by rw [hmZ]; exact hxm) hparams hmparams (by push_cast; exact hword)
        (by push_cast; rw [hmZ]; rw [hyZ] at hb; linarith)
      refine WordLink.bound_mono L L _ _ le_rfl ?_ hlift
      push_cast
      have := ScaleNumbers.small_output x y m (by exact_mod_cast hx) (by positivity)
        (by exact_mod_cast hyx) (by positivity) (by rw [hmZ]; linarith)
      exact this
    · push Not at hmsmall
      have hword := IH m (by omega) hmL
      obtain ⟨hx114, hn⟩ := ScaleNumbers.huge_window x hmsmall
      have hx20 : 2^20 < x := lt_trans (by norm_num) hx114
      obtain ⟨-, hnx, -, hyn, hm64⟩ := ScaleNumbers.large_window x hx20
      have hb := ScaleNumbers.large_budget x hx hmsmall
      simp only at hb
      have hr1 : 1 ≤ 2^64*(y+1)^4 := Nat.one_le_iff_ne_zero.2 (by positivity)
      have hlift := LargeStep.lift m L x y (2^64*(y+1)^4) (by omega) (by omega) hmL.le hr1 hLx
        (by rw [hmZ]; exact hxm) hparams hmparams (by push_cast; exact hword)
        (by push_cast; rw [hmZ]; rw [hyZ] at hb; linarith)
      refine WordLink.bound_mono L L _ _ le_rfl ?_ hlift
      push_cast
      have hnxZ : (2:ℤ)^(Nat.log 2 x) ≤ x := by exact_mod_cast hnx
      have hm64Z : (m:ℤ) ≤ 64*x := by exact_mod_cast hm64
      exact ScaleNumbers.large_output x y m (Nat.log 2 x) (by exact_mod_cast (by omega : 1 ≤ x))
        (by positivity) (by exact_mod_cast hyn) hn hnxZ (by positivity) hm64Z

theorem quartic (k : ℕ) (hprev : Closure.Earlier k) :
    ∀ L, 2 ≤ L → L < k → WordLink.Bound L (2^64*((CheckTable.log2up L : ℤ)+1)^4) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
      intro hL2 hLk
      exact induction_step k L hprev hL2 hLk (fun m hm2 hmL ↦ ih m hmL hm2 (by omega))

end BMO9.GlobalBounds
