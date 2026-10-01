/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Table

/-!
# BMO #9, port of Rocq `Module UniqueTable` (BMO9.v lines 1133-1189, ccz181078)

The built table has at most one entry per level.
-/

namespace BMO9.UniqueTable

open Table

theorem odd_power_injective (s t : ℕ) (r u : ℤ) (hr : Odd r) (hu : Odd u)
    (h : 2^s*r = 2^t*u) : s = t ∧ r = u := by
  induction s generalizing t with
  | zero =>
      rcases t with _ | t
      · simpa using h
      · exfalso
        simp only [pow_zero, one_mul] at h
        rw [h, pow_succ] at hr
        exact (Int.not_even_iff_odd.2 hr) ⟨2^t*u, by ring⟩
  | succ s ih =>
      rcases t with _ | t
      · exfalso
        simp only [pow_zero, one_mul] at h
        rw [← h, pow_succ] at hu
        exact (Int.not_even_iff_odd.2 hu) ⟨2^s*r, by ring⟩
      · have : 2^s*r = 2^t*u := by
          rw [pow_succ, pow_succ] at h; linarith
        obtain ⟨h1, h2⟩ := ih t this
        exact ⟨by omega, h2⟩

theorem separated_unique (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) (t : ℕ) (u : ℤ)
    (h1 : Separated k x s r) (h2 : Separated k x t u) : s = t ∧ r = u :=
  odd_power_injective s t r u h1.2.2.2 h2.2.2.2 (h1.2.2.1.symm.trans h2.2.2.1)

theorem built_unique {k f} (H : Built k f) : ∀ g, Built k g → f = g := by
  induction H with
  | root => intro g hg; cases hg; rfl
  | one _ ih =>
      intro g hg; cases hg with
      | one h' => cases ih _ h'; rfl
      | even h' _ => cases ih _ h'
      | lookup_one h' _ _ _ => cases ih _ h'
      | lookup_two h' _ _ _ => cases ih _ h'
  | even _ he ih =>
      intro g hg; cases hg with
      | one h' => cases ih _ h'
      | even h' _ => cases ih _ h'; rfl
      | lookup_one h' _ ho _ => cases ih _ h'; simp_all
      | lookup_two h' _ ho _ => cases ih _ h'; simp_all
  | lookup_one _ hs ho _ ih ih' =>
      intro g hg; cases hg with
      | one h' => cases ih _ h'
      | even h' he => cases ih _ h'; simp_all
      | lookup_one h' hs' _ hsm =>
          cases ih _ h'
          obtain ⟨rfl, rfl⟩ := separated_unique _ _ _ _ _ _ hs hs'
          cases ih' _ hsm; rfl
      | lookup_two h' hs' _ hsm =>
          cases ih _ h'
          obtain ⟨rfl, rfl⟩ := separated_unique _ _ _ _ _ _ hs hs'
          cases ih' _ hsm
  | lookup_two _ hs ho _ ih ih' =>
      intro g hg; cases hg with
      | one h' => cases ih _ h'
      | even h' he => cases ih _ h'; simp_all
      | lookup_one h' hs' _ hsm =>
          cases ih _ h'
          obtain ⟨rfl, rfl⟩ := separated_unique _ _ _ _ _ _ hs hs'
          cases ih' _ hsm
      | lookup_two h' hs' _ hsm =>
          cases ih _ h'
          obtain ⟨rfl, rfl⟩ := separated_unique _ _ _ _ _ _ hs hs'
          cases ih' _ hsm; rfl

end BMO9.UniqueTable
