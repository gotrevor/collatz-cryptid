/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.TableBridge

/-!
# BMO #9, port of Rocq `Module Cubic` (BMO9.v lines 2385-2469, ccz181078)

Every built entry has at most `4 k^3` steps.  Rocq `Z.log2_up` is `CheckTable.log2up`
(`Nat.clog 2`).  The pure arithmetic lemmas are proved over `ℕ` and stated over `ℤ`.
-/

namespace BMO9.Cubic

open Table

theorem cubic_exp_nat (k : ℕ) (hk : 16 ≤ k) : 12*k^3+4 < 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have h1 : 16*k^2 ≤ k^3 := by rw [pow_succ k 2]; nlinarith
      have h2 : 16*k ≤ k^2 := by nlinarith
      rw [pow_succ 2 k]; nlinarith

theorem cubic_exp (k : ℕ) (hk : 16 ≤ k) : 12*(k:ℤ)^3+4 < 2^k := by
  exact_mod_cast cubic_exp_nat k hk

theorem cubic_exp2_nat (x : ℕ) (hx : 16 ≤ x) : 2048*x^3 ≤ 12*2^(2*x-2) := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
      have h1 : 16*x^2 ≤ x^3 := by rw [pow_succ x 2]; nlinarith
      have h2 : 16*x ≤ x^2 := by nlinarith
      rw [show 2*(x+1)-2 = (2*x-2)+2 by omega, pow_add]; nlinarith

theorem cubic_exp2 (x : ℕ) (hx : 16 ≤ x) : 2048*(x:ℤ)^3 ≤ 12*2^(2*x-2) := by
  exact_mod_cast cubic_exp2_nat x hx

theorem lookup_index_nat (k s : ℕ) (_hk : 2 ≤ k) (_hs : 1 ≤ s) (hp : 2^s ≤ 24*k^3+4) :
    s ≤ 3*CheckTable.log2up k + 4 := by
  set x := CheckTable.log2up k
  have hhi : k ≤ 2^x := Nat.le_pow_clog (by norm_num) k
  have hE : 2^(3*x+5) = 32*(2^x)^3 := by ring
  have h1 : 1 ≤ 2^x := Nat.one_le_two_pow
  have hc : k^3 ≤ (2^x)^3 := Nat.pow_le_pow_left hhi 3
  have h3 : 1 ≤ (2^x)^3 := Nat.one_le_pow _ _ h1
  have HL : 2^s < 2^(3*x+5) := by rw [hE]; omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 HL
  omega

theorem lookup_index (k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (hp : (2:ℤ)^s ≤ 24*(k:ℤ)^3+4) :
    s ≤ 3*CheckTable.log2up k + 4 :=
  lookup_index_nat k s hk hs (by exact_mod_cast hp)

theorem growth (k s : ℕ) (hk : 65536 ≤ k) (hs : 1 ≤ s) (hp : (2:ℤ)^s ≤ 24*(k:ℤ)^3+4) :
    1 + 4*(s:ℤ)^3 ≤ 12*(k:ℤ)^2 := by
  have hsb := lookup_index k s (by omega) hs hp
  set x := CheckTable.log2up k with hxdef
  have hx : 16 ≤ x := by
    by_contra hcon
    have : x ≤ 15 := by omega
    have := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).1 this
    norm_num at this; omega
  have hlo : 2^(x-1) < k := by
    by_contra hcon
    have := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).2 (not_lt.1 hcon)
    have h' : CheckTable.log2up k ≤ x - 1 := this
    omega
  have HE := cubic_exp2_nat x hx
  have hsmall : 1 + 4*s^3 ≤ 2048*x^3 := by
    have : s^3 ≤ (4*x)^3 := Nat.pow_le_pow_left (by omega) 3
    have : 1 ≤ x^3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have HP : 2^(2*x-2) = 2^(x-1)*2^(x-1) := by rw [← pow_add]; congr 1; omega
  rw [HP] at HE
  have : 2^(x-1)*2^(x-1) ≤ k*k := Nat.mul_le_mul hlo.le hlo.le
  have hn : 1 + 4*s^3 ≤ 12*k^2 := by nlinarith
  exact_mod_cast hn

theorem lookup_h (k : ℕ) (x : Pair) (e : ℤ) (s : ℕ) (r : ℤ) (hb : Built k (.two x e))
    (hs : Separated k x s r) (he : e ≤ 4*(k:ℤ)^3) : (2:ℤ)^s ≤ 24*(k:ℤ)^3+4 := by
  obtain ⟨-, -, hh, hr⟩ := hs
  obtain ⟨⟨he0, ⟨⟨-, -, -, -, hb1, -⟩, -, hc0⟩, hmass⟩, -⟩ := built_valid hb
  simp only [h] at hh
  have hP : (0:ℤ) < 2^s := by positivity
  have : 1 ≤ r := by
    obtain ⟨j, rfl⟩ := hr
    by_contra hcon
    have : (2:ℤ)^s*(2*j+1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP.le (by omega)
    omega
  nlinarith

theorem built_cubic (k : ℕ) (f : Entry) (H : Built k f) : steps f ≤ 4*(k:ℤ)^3 := by
  induction H with
  | root => simp [steps]
  | one _ ih =>
      simp only [steps] at ih ⊢; push_cast
      rename_i k _ _ _
      have : (0:ℤ) ≤ k := by positivity
      nlinarith
  | even _ _ ih =>
      simp only [steps] at ih ⊢; push_cast
      rename_i k _ _ _ _
      have : (0:ℤ) ≤ k := by positivity
      nlinarith
  | @lookup_one k x e s r v f hb hs ho hsm ih ihs =>
      by_cases hbase : k+1 ≤ 65536
      · exact (TableBridge.all_base (k+1) _ (by omega) hbase
          (Built.lookup_one hb hs ho hsm)).1.1
      · simp only [steps] at ih ihs ⊢
        have hg := growth k s (by omega) hs.1 (lookup_h _ _ _ _ _ hb hs ih)
        push_cast
        have : (0:ℤ) ≤ k := by positivity
        nlinarith
  | @lookup_two k x e s r y f hb hs ho hsm ih ihs =>
      by_cases hbase : k+1 ≤ 65536
      · exact (TableBridge.all_base (k+1) _ (by omega) hbase
          (Built.lookup_two hb hs ho hsm)).1.1
      · simp only [steps] at ih ihs ⊢
        have hg := growth k s (by omega) hs.1 (lookup_h _ _ _ _ _ hb hs ih)
        push_cast
        have : (0:ℤ) ≤ k := by positivity
        nlinarith

end BMO9.Cubic
