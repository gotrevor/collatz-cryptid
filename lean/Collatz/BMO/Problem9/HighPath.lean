/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Block

/-!
# BMO #9, port of Rocq `Module HighPath` (BMO9.v lines 2743-2864, ccz181078)

Certified high paths, adjacent exact descent, and the root-counting bound on path length.
The level `m` and depth bound `D` are exponents, hence `ℕ`; `M`, `B` stay in `ℤ`.
-/

namespace BMO9.HighPath

open Block

def certified (m D : ℕ) (M B : ℤ) (z : Summary) : Prop :=
  ∃ d : ℕ, d ≤ D ∧ z.scale = 2^d ∧ z.scale ≤ z.sc ∧ z.sc ≤ 2*z.scale ∧
    0 < z.offset ∧ z.offset ≤ z.scale*(2*M+2) ∧ (m:ℤ) < z.added ∧ z.added ≤ M ∧
    2*z.offset ≤ z.sc*(3*z.added + 2*B + 6)

inductive path (m D : ℕ) (M B : ℤ) : List Summary → ℤ → ℤ → Prop
  | stop (S H : ℤ) : (2:ℤ)^(m+1) ∣ H → path m D M B [] S H
  | step (z : Summary) (zs : List Summary) (S H H' : ℤ) : (2:ℤ)^(m+1) ∣ H →
      certified m D M B z → denotes z S H (S + z.added) H' →
      path m D M B zs (S + z.added) H' → path m D M B (z :: zs) S H

theorem path_div {m D : ℕ} {M B : ℤ} {zs : List Summary} {S H : ℤ}
    (hp : path m D M B zs S H) : (2:ℤ)^(m+1) ∣ H := by
  cases hp <;> assumption

inductive chain (m D : ℕ) (M B : ℤ) : List Summary → Prop
  | one (z : Summary) : certified m D M B z → chain m D M B [z]
  | more (z z' : Summary) (zs : List Summary) : certified m D M B z →
      z.sc*z'.offset = z'.sc*(z.offset - z.sc*z.added) →
      chain m D M B (z' :: zs) → chain m D M B (z :: z' :: zs)

theorem adjacent (m D : ℕ) (M B : ℤ) (z z' : Summary) (S H0 H1 H2 : ℤ)
    (hz : certified m D M B z) (hz' : certified m D M B z')
    (hH0 : (2:ℤ)^(m+1) ∣ H0) (hH1 : (2:ℤ)^(m+1) ∣ H1) (hH2 : (2:ℤ)^(m+1) ∣ H2)
    (h0 : denotes z S H0 (S + z.added) H1)
    (h1 : denotes z' (S + z.added) H1 (S + z.added + z'.added) H2)
    (hbudget : 2^(2*D)*(12*M+8) < (2:ℤ)^(m+1)) :
    z.sc*z'.offset = z'.sc*(z.offset - z.sc*z.added) := by
  obtain ⟨d0, hd0, hQ0, hA0, hA0', hC0, hC0', hM0, hM0', -⟩ := hz
  obtain ⟨d1, hd1, hQ1, hA1, hA1', hC1, hC1', -, -, -⟩ := hz'
  have e0 := h0.2
  have e1 := h1.2
  rw [hQ0] at hA0 hA0' hC0' e0
  rw [hQ1] at hA1 hA1' hC1' e1
  have p0 : (0:ℤ) < 2^d0 := by positivity
  have p1 : (0:ℤ) < 2^d1 := by positivity
  have hm0 : (0:ℤ) ≤ m := by positivity
  exact dyadic_descent m D d0 d1 S H0 H1 H2 z.sc z'.sc z.hc z'.hc z.offset z'.offset z.added M
    hd0 hd1 (by linarith) hM0' (by linarith) hA0' (by linarith) hA1' hC0.le hC0' hC1.le hC1'
    hH0 hH1 hH2 e0 e1 hbudget

theorem path_chain (m D : ℕ) (M B : ℤ) (zs : List Summary) (S H : ℤ)
    (hbudget : 2^(2*D)*(12*M+8) < (2:ℤ)^(m+1)) (hp : path m D M B zs S H) (hne : zs ≠ []) :
    chain m D M B zs := by
  induction hp with
  | stop => exact absurd rfl hne
  | step z zs S H H' hH hz hstep htail ih =>
    cases zs with
    | nil => exact chain.one z hz
    | cons z' zs =>
      cases htail with
      | step _ _ _ _ H2 hH1 hz' hstep' htail' =>
        refine chain.more z z' zs hz ?_ (ih (by simp))
        exact adjacent m D M B z z' S H H' H2 hz hz' hH hH1 (path_div htail') hstep hstep'
          hbudget

/-- Numerators of successive positive roots, all over the first root's denominator. -/
inductive roots (A B m : ℤ) : ℤ → ℕ → Prop
  | one (f : ℤ) : 0 < f → roots A B m f 0
  | more (f g : ℤ) (n : ℕ) : 3*g ≤ f + 2*A*(B+3) → g < f - A*m →
      roots A B m g n → roots A B m f (n+1)

theorem roots_function {A B m f : ℤ} {n : ℕ} (hr : roots A B m f n) :
    ∃ v : ℕ → ℤ, v 0 = f ∧ 0 < v n ∧
      ∀ i < n, 3*v (i+1) ≤ v i + 2*A*(B+3) ∧ v (i+1) < v i - A*m := by
  induction hr with
  | one f hf => exact ⟨fun _ ↦ f, rfl, hf, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | more f g n hshrink hdrop _ ih =>
    obtain ⟨v, hv0, hvn, hsteps⟩ := ih
    refine ⟨fun i ↦ match i with | 0 => f | j+1 => v j, rfl, hvn, ?_⟩
    intro i hi
    match i with
    | 0 => simp only; rw [hv0]; exact ⟨hshrink, hdrop⟩
    | i+1 => exact hsteps i (by omega)

theorem roots_count (A B m f : ℤ) (n t q : ℕ) (V : ℤ) (hA : 0 < A) (hB : 0 ≤ B) (hm : 0 < m)
    (hV : 0 ≤ V) (hpow : V ≤ 3^t) (hq : B + 4 ≤ q*m) (hf : f ≤ A*V) (hr : roots A B m f n) :
    n < t + q := by
  obtain ⟨v, hv, hlast, hsteps⟩ := roots_function hr
  exact high_count v A B V m t q n hA hB hm hV hpow hq (hv ▸ hf) hlast
    (fun i hi ↦ (hsteps i hi).1) (fun i hi ↦ (hsteps i hi).2)

theorem chain_roots (m D : ℕ) (M B : ℤ) (zs : List Summary) (hchain : chain m D M B zs) :
    ∀ z rest, zs = z :: rest → ∀ A f : ℤ, 0 < A → A*z.offset = z.sc*f →
      roots A B m f rest.length := by
  induction hchain with
  | one z hz =>
    intro z0 rest heq A f hA hroot
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    obtain ⟨d, -, hQ, hsc, -, hc, -⟩ := hz
    have : (0:ℤ) < 2^d := by positivity
    refine roots.one f ?_
    by_contra hneg; push Not at hneg
    nlinarith
  | more z z' zs hz hdescent _ ih =>
    intro z0 rest heq A f hA hroot
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    obtain ⟨d, -, hQ, hsc, -, -, -, hmass, -, hcontract⟩ := hz
    have : (0:ℤ) < 2^d := by positivity
    have hnext : A*z'.offset = z'.sc*(f - A*z.added) := by
      have := propagate_root A f z.sc z.offset z'.sc z'.offset 0 z.added (by linarith)
        (by simpa using hroot) hdescent
      simpa using this
    change roots A B m f (zs.length + 1)
    refine roots.more f (f - A*z.added) _ ?_ ?_ (ih z' zs rfl A (f - A*z.added) hA hnext)
    · have h1 := mul_le_mul_of_nonneg_left hcontract hA.le
      nlinarith
    · have := mul_lt_mul_of_pos_left hmass hA
      linarith

theorem path_count (m D : ℕ) (M B : ℤ) (zs : List Summary) (S H : ℤ) (t q : ℕ) (hm : 0 < m)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hpow : 2*M + 2 ≤ 3^t) (hq : B + 4 ≤ q*(m:ℤ))
    (hbudget : 2^(2*D)*(12*M+8) < (2:ℤ)^(m+1)) (hp : path m D M B zs S H) :
    zs.length < t + q + 1 := by
  cases zs with
  | nil => simp
  | cons z rest =>
    have hchain := path_chain m D M B (z :: rest) S H hbudget hp (by simp)
    cases hp with
    | step _ _ _ _ H' _ hz _ _ =>
      obtain ⟨d, -, hQ, hA, -, hC, hC', -⟩ := hz
      have : (0:ℤ) < 2^d := by positivity
      have hr := chain_roots m D M B _ hchain z rest rfl z.sc z.offset (by linarith) rfl
      have := roots_count z.sc B m z.offset rest.length t q (2*M+2) (by linarith) hB
        (by exact_mod_cast hm) (by linarith) hpow hq (by nlinarith) hr
      simp only [List.length_cons]
      omega

end BMO9.HighPath
