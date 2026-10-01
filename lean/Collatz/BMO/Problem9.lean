/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Bridge
import Collatz.BMO.Problem9.Final

/-!
# BMO #9: the first obstruction

The published rules act on infinite streams of natural numbers.  A finite list here denotes
that list followed by infinitely many zeros.  The step function keeps the published four
branches exactly; different lists with trailing zeros represent the same stream.

This file isolates the exact precursor to halting and the known sum-modulo-three invariant.
The latter does not solve the problem: `[1, 2, 0]` satisfies the invariant but immediately
creates a halting prefix.  Reachability is the missing content.
-/

namespace BMO9

def coord (s : List ℕ) (i : ℕ) : ℕ := (s[i]?).getD 0

def step (s : List ℕ) : Option (List ℕ) :=
  let a := coord s 0
  let b := coord s 1
  let c := coord s 2
  let rest := s.drop 3
  if a = 0 then some ((3 + b + c) :: rest)
  else if a = 1 then
    if b = 0 then none else some ((b - 1) :: 0 :: 1 :: (c + 1) :: rest)
  else some ((a - 2) :: (b + 1) :: (c + 1) :: rest)

def orbit : ℕ → Option (List ℕ)
  | 0 => some []
  | n + 1 => (orbit n).bind step

/-- The published question asks whether this statement holds. -/
def Nonhalting : Prop := ∀ n, orbit n ≠ none

theorem step_halts_iff (s : List ℕ) :
    step s = none ↔ coord s 0 = 1 ∧ coord s 1 = 0 := by
  simp only [step]
  split_ifs with h0 h1 h2 <;> simp_all

/-- A live step can create the halting prefix only from a prefix `(1, 2)`. -/
theorem step_creates_halt_iff (s t : List ℕ) (h : step s = some t) :
    (coord t 0 = 1 ∧ coord t 1 = 0) ↔
      (coord s 0 = 1 ∧ coord s 1 = 2) := by
  simp only [step] at h
  split_ifs at h <;> cases h <;> simp_all [coord] <;> omega

example : step [1, 2, 0] = some [1, 0, 1, 1] := by decide
example : ([1, 2, 0] : List ℕ).sum % 3 = 0 := by decide

example : orbit 0 = some [] := by decide
example : orbit 1 = some [3] := by decide
example : orbit 2 = some [1, 1, 1] := by decide
example : orbit 3 = some [0, 0, 1, 2] := by decide

theorem step_sum_mod (s t : List ℕ) (h : step s = some t) :
    t.sum % 3 = s.sum % 3 := by
  cases s with
  | nil =>
      simp [step, coord] at h
      subst t
      decide
  | cons a tail =>
      cases tail with
      | nil =>
          simp [step, coord] at h
          split_ifs at h <;> cases h <;> simp_all <;> omega
      | cons b tail =>
          cases tail with
          | nil =>
              simp [step, coord] at h
              split_ifs at h <;> cases h <;> simp_all <;> omega
          | cons c r =>
              simp [step, coord] at h
              split_ifs at h <;> cases h <;> simp_all <;> omega

theorem orbit_sum_mod (n : ℕ) (s : List ℕ) (h : orbit n = some s) :
    s.sum % 3 = 0 := by
  induction n generalizing s with
  | zero =>
      simp [orbit] at h
      subst s
      simp
  | succ n ih =>
      simp only [orbit] at h
      cases ho : orbit n with
      | none => simp [ho] at h
      | some p =>
          have hp : p.sum % 3 = 0 := ih p ho
          simp [ho] at h
          exact (step_sum_mod p s h).trans hp

/-! ## The headline

BMO#9 as posed on the [BMO wiki](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) §9,
in the style of `google-deepmind/formal-conjectures`, so it can anchor a `formal_proof` link.
A configuration is a sequence `ℕ → ℕ`.  The four rules, for `a b c ∈ ℕ` and a tail `r`:

* `(0, a, c, r) ↦ (3 + a + c, r)`
* `(1, 0, r) ↦ Halt`
* `(1, 1 + a, c, r) ↦ (a, 0, 1, 1 + c, r)`
* `(2 + a, b, c, r) ↦ (a, 1 + b, 1 + c, r)`

The orbit of the all-zero sequence never reaches `Halt`.  The second branch of `x_rec` also covers
the halting prefix `(1, 0, …)` with an arbitrary value.  This is harmless: the conclusion says that
prefix never occurs, and the steps before its first occurrence follow the published rules. -/

theorem beaver_math_olympiad_problem_9
    (x : ℕ → ℕ → ℕ)
    (x_ini : x 0 = fun _ ↦ 0)
    (x_rec : ∀ n, x (n + 1) =
      if x n 0 = 0 then
        fun i ↦ if i = 0 then 3 + x n 1 + x n 2 else x n (i + 2)
      else if x n 0 = 1 then
        fun i ↦ if i = 0 then x n 1 - 1 else if i = 1 then 0 else if i = 2 then 1
          else if i = 3 then 1 + x n 2 else x n (i - 1)
      else
        fun i ↦ if i = 0 then x n 0 - 2 else if i ≤ 2 then 1 + x n i else x n i) :
    ¬ ∃ n, x n 0 = 1 ∧ x n 1 = 0 := by
  rintro ⟨n, hn⟩
  exact Bridge.forever x (fun n ↦ x_rec n) x_ini
    (Prefix.single_returns Final.G_returns) n hn

end BMO9
