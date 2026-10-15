/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic
import Collatz.Bigfoot.Clock

/-!
# The Maze gate on Bigfoot's counter

Question (cross-lane review, T1(iii)): is V6's reserve `k` (Shawn's counter `a`, under
`φ(a, b, c) = (a, 2b − 1, 2c + 1, P1)`) a function of the clock phase and finitely many base-3
digits of `b`?  If it were, the `KPosCascade` obligations would be within the Terras horizon.

Answer: **no**.  The *increment* of `a` is local (`walk_local`: a function of `b mod 6`, i.e. of the
phase parity and `b mod 3`), but `a` itself is not a function of `(n mod 4, b mod 3^j)` for any
`j ≤ 8` (`a_not_local`, explicit collisions on the orbit).  So the counter is the partial sum of a
digit-driven walk along one orbit: its positivity is the single-orbit wall, and `KPosCascade` is the
open problem in costume.
-/

namespace Collatz.Bigfoot.Dyn

/-- The walk increment of `a` at residue `r = b mod 6` (`0, +1, −1, 0, +1, 0`). -/
def walkInc (r : ℕ) : ℤ := if r = 1 ∨ r = 4 then 1 else if r = 2 then -1 else 0

/-- **The increment is local**: one step changes `a` by `walkInc (b mod 6)`. -/
theorem walk_local (s t : Dyn) (h : step s = some t) :
    (t.a : ℤ) = s.a + walkInc (s.b % 6) := by
  obtain ⟨a, b, c⟩ := s
  dsimp only [step] at h
  split_ifs at h with h0 h1 h2 ha h3 h4 <;> (simp only [Option.some.injEq] at h) <;> subst h <;>
    simp only [walkInc] <;> split_ifs <;> omega

/-- A collision certificate: orbit points `n₁, n₂` with the same phase and the same `b mod 3^j`,
but different `a`. -/
def collides (j n₁ n₂ : ℕ) : Bool :=
  match orbit n₁, orbit n₂ with
  | some s₁, some s₂ => n₁ % 4 == n₂ % 4 && s₁.b % 3 ^ j == s₂.b % 3 ^ j && s₁.a != s₂.a
  | _, _ => false

theorem not_local_of_collides (j n₁ n₂ : ℕ) (h : collides j n₁ n₂ = true) :
    ¬ ∃ f : ℕ → ℕ → ℕ, ∀ n s, orbit n = some s → s.a = f (n % 4) (s.b % 3 ^ j) := by
  rintro ⟨f, hf⟩
  unfold collides at h
  cases h₁ : orbit n₁ with
  | none => simp [h₁] at h
  | some s₁ =>
    cases h₂ : orbit n₂ with
    | none => simp [h₁, h₂] at h
    | some s₂ =>
      simp only [h₁, h₂, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨hp, hb⟩, ha⟩ := h
      exact ha (by rw [hf _ _ h₁, hf _ _ h₂, hp, hb])

/-- **The Maze gate fails for `j ≤ 8`**: `a` is not a function of `(n mod 4, b mod 3^j)` along the
orbit.  Collisions (checked by kernel evaluation): `j = 1: (6, 10)`, `2: (6, 14)`,
`3, 4: (17, 25)`, `5: (5, 49)`, `6: (68, 88)`, `7: (82, 126)`, `8: (292, 360)`. -/
theorem a_not_local (j : ℕ) (hj : 1 ≤ j ∧ j ≤ 8) :
    ¬ ∃ f : ℕ → ℕ → ℕ, ∀ n s, orbit n = some s → s.a = f (n % 4) (s.b % 3 ^ j) := by
  obtain ⟨h1, h8⟩ := hj
  interval_cases j
  · exact not_local_of_collides 1 6 10 (by decide +kernel)
  · exact not_local_of_collides 2 6 14 (by decide +kernel)
  · exact not_local_of_collides 3 17 25 (by decide +kernel)
  · exact not_local_of_collides 4 17 25 (by decide +kernel)
  · exact not_local_of_collides 5 5 49 (by decide +kernel)
  · exact not_local_of_collides 6 68 88 (by decide +kernel)
  · exact not_local_of_collides 7 82 126 (by decide +kernel)
  · exact not_local_of_collides 8 292 360 (by decide +kernel)

end Collatz.Bigfoot.Dyn
