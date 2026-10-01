/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.WordLink

/-!
# BMO #9, port of Rocq `Module BoundaryBound` (BMO9.v lines 2560-2657, ccz181078)

A boundary chain either returns or produces a long trace of continuing kernels; a word bound
rules out the latter.
-/

namespace BMO9.BoundaryBound

open Table WordLibrary

theorem constant_action (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (e : ℤ)
    (hsep : Separated k x s r) (hb : Built s (.two y e)) :
    Action ⟨s, y⟩ (x.b + x.c) x.b ((next x s r y).b + (next x s r y).c) (next x s r y).b := by
  obtain ⟨⟨he, hy, hmass⟩, -⟩ := built_valid hb
  refine ⟨?_, ?_, ?_⟩
  · rw [next_mass]; simp only [gain]; ring
  · have hd := delta_exact k x s r y hsep hy
    simp only [next, h] at hd ⊢
    linear_combination hd
  · obtain ⟨-, -, hh, t, ht⟩ := hsep
    refine ⟨t, ?_⟩
    simp only [h] at hh
    rw [← ht]; linarith

theorem small_separated (k : ℕ) (x : Pair) (L : ℕ) (hx : Sane k x) (hL : 1 ≤ L)
    (hdepth : x.d + L < k) (hbound : h x < 2^L) (he : even_head k x = false) :
    ∃ s r, Separated k x s r ∧ s < L := by
  obtain ⟨hd, hp, hp2, ho, hb, hc⟩ := hx
  have hpos : 0 < h x := by simp only [h]; omega
  have hbodd : Odd x.b := by
    have hdk : x.d < k := by omega
    simp only [even_head, head_constant, if_pos hdk, beq_eq_false_iff_ne] at he
    exact Int.odd_iff.2 (by omega)
  obtain ⟨s, m, hm, hfac⟩ := Nat.exists_eq_two_pow_mul_odd (n := (h x).toNat) (by omega)
  have hfac' : h x = 2^s*(m:ℤ) := by
    have : ((h x).toNat : ℤ) = ((2^s*m : ℕ) : ℤ) := by rw [← hfac]
    rw [Int.toNat_of_nonneg hpos.le] at this; rw [this]; push_cast; ring
  have hmo : Odd (m:ℤ) := by exact_mod_cast hm
  have hm1 : (1:ℤ) ≤ m := by obtain ⟨j, hj⟩ := hmo; omega
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_mul] at hfac'
      simp only [h] at hfac'
      obtain ⟨a, ha⟩ := hbodd; obtain ⟨v, hv⟩ := hmo; omega
    · exact h0
  have hsL : s < L := by
    have h1 : (2:ℤ)^s < 2^L := by
      have : (2:ℤ)^s ≤ 2^s*m := le_mul_of_one_le_right (by positivity) hm1
      linarith
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1:ℤ) < 2)).1 h1
  exact ⟨s, m, ⟨hs1, by omega, hfac', hmo⟩, hsL⟩

/-- The budgets pay for every continuing call. -/
theorem boundary_or_word (k L : ℕ) (D M : ℤ) (hL : 1 ≤ L) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hlib : ∀ s, 1 ≤ s → s ≤ L → ∃ f, Built s f)
    (hparams : ∀ s y e, 1 ≤ s → s ≤ L → Built s (.two y e) → (y.d:ℤ) ≤ D ∧ y.b + y.c + 2 ≤ M) :
    ∀ (n : ℕ) (x : Pair), Sane k x → (x.d:ℤ) + n*D + L < k →
      2*(x.b + x.c + n*M) + 3 < 2^L →
      (∃ e m, Boundary Built k x e m) ∨
      (∃ word : List Kernel, word.length = n ∧ (∀ z ∈ word, Continuing z ∧ z.index ≤ L) ∧
        Trace word (x.b + x.c) x.b) := by
  intro n
  induction n with
  | zero => intro x _ _ _; exact Or.inr ⟨[], rfl, by simp, Trace.nil _ _⟩
  | succ n ih =>
      intro x hx hdepth hmass
      cases he : even_head k x with
      | true => exact Or.inl ⟨1, 1, Boundary.even he⟩
      | false =>
          have hnD : (0:ℤ) ≤ (n:ℤ)*D := by positivity
          have hnM : (0:ℤ) ≤ ((n+1 : ℕ):ℤ)*M := by positivity
          have hxdepth : x.d + L < k := by push_cast at hdepth; nlinarith
          have hxbound : h x < 2^L := by
            obtain ⟨-, -, -, -, hb, hc⟩ := hx
            simp only [h]; linarith
          obtain ⟨s, r, hsep, hsL⟩ := small_separated k x L hx hL hxdepth hxbound he
          obtain ⟨f, hb⟩ := hlib s hsep.1 hsL.le
          cases f with
          | one v e => exact Or.inl ⟨1+e, 1, Boundary.one hsep he hb⟩
          | two y e =>
              obtain ⟨⟨he0, hy, hysum⟩, -⟩ := built_valid hb
              obtain ⟨hnext, hc⟩ := next_sane k x s r y hx hsep hy
              have HP := TableBridge.lookup_parity k x s r y hx hsep hy
              cases hpar : even_head s y with
              | true =>
                  exact Or.inl ⟨1+e+1, 2, Boundary.two hsep he hb
                    (Boundary.even (HP.trans hpar))⟩
              | false =>
                  obtain ⟨hDy, hMy⟩ := hparams s y e hsep.1 hsL.le hb
                  rcases ih (next x s r y) hnext
                      (by simp only [next]; push_cast at hdepth ⊢; linarith)
                      (by rw [next_mass]; push_cast at hmass; linarith) with
                    ⟨f, m, hret⟩ | ⟨word, hlen, hall, htrace⟩
                  · exact Or.inl ⟨1+e+f, 1+m, Boundary.two hsep he hb hret⟩
                  · refine Or.inr ⟨⟨s, y⟩ :: word, by simp [hlen], ?_, ?_⟩
                    · intro z hz
                      rcases List.mem_cons.1 hz with rfl | hz
                      · exact ⟨⟨e, hb, hsep.1, hpar⟩, hsL.le⟩
                      · exact hall z hz
                    · exact Trace.cons (constant_action k x s r y e hsep hb) htrace

theorem returns_of_bound (k : ℕ) (x : Pair) (L : ℕ) (D M : ℤ) (n : ℕ) (hL : 1 ≤ L)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hx : Sane k x)
    (hlib : ∀ s, 1 ≤ s → s ≤ L → ∃ f, Built s f)
    (hparams : ∀ s y e, 1 ≤ s → s ≤ L → Built s (.two y e) → (y.d:ℤ) ≤ D ∧ y.b + y.c + 2 ≤ M)
    (hwords : WordLink.Bound L ((n:ℤ) - 1)) (hdepth : (x.d:ℤ) + n*D + L < k)
    (hmass : 2*(x.b + x.c + n*M) + 3 < 2^L) : ∃ e m, Boundary Built k x e m := by
  rcases boundary_or_word k L D M hL hD hM hlib hparams n x hx hdepth hmass with
    hret | ⟨word, hlen, hall, htrace⟩
  · exact hret
  · have := hwords word _ _ hall htrace
    rw [hlen] at this; omega

end BMO9.BoundaryBound
