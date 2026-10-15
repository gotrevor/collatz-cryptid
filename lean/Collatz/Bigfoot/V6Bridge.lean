/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic
import Collatz.Bigfoot.V6KPos
import Collatz.Bigfoot.Clock

/-!
# V6 ↔ Ligocki: what `KPosCascade` says in `(a, b, c)` coordinates

`Classification.lean` describes V6 as "a transformed view" of Ligocki's `Dyn` via
`φ(a, b, c) = (k := a, a := 2b − 1, b := 2c + 1, P1)`.  This file proves it.  One `Dyn` step from
`s` is a *segment* of V6 steps from `φ s` to `φ (step s)` (`segment`): `⌊b/6⌋` B/S pairs (each
`a −= 12`, `b += 16`) and then a tail of 2–3 rules chosen by `b mod 6`.  The only `k`-decrement
firings, `(P1, a = 9)` (B-coll) and `(P1, a = 3)` (D-W), occur exactly in the segments of steps with
`b ≡ 5` and `b ≡ 2 (mod 6)`, and there `k = a`.

Consequence (**`kPosCascade_iff_margin2`**): the repo's crux `KPosCascade` is *equivalent* to

  `Margin2 : ∀ n s, Dyn.orbit n = some s → s.b % 6 ∈ {2, 5} → 2 ≤ s.a`,

a single-orbit walk-positivity statement with margin 2.  This is in the same form as Bigfoot's
non-halting `∀ n s, orbit n = some s → s.b % 6 = 2 → 1 ≤ s.a` (`Classification.lean`), and
formally stronger: it also asks for margin at the harmless `b ≡ 5` steps, where V6's B-coll
passes through `k − 1` before Q-kpp restores it.  So `KPosCascade` is not "equivalent to the
holdout" as an identity of statements, but `Margin2 → nonhalt` (`margin2_nonhalt`).  Both are the
open problem in costume: the counter is the partial sum of a digit-driven walk
(`Dyn.walk_local`) that is not itself digit-determined (`Dyn.a_not_local`).
-/

namespace Collatz.Bigfoot.V6

open Pat

/-- `n` V6 steps from `σ` (step first, so that segments compose). -/
def run : ℕ → State → Option State
  | 0, σ => some σ
  | n + 1, σ => (step σ).bind (run n)

theorem run_zero (σ : State) : run 0 σ = some σ := rfl

theorem run_succ (n : ℕ) (σ : State) : run (n + 1) σ = (step σ).bind (run n) := rfl

theorem run_add (m n : ℕ) (σ : State) : run (m + n) σ = (run m σ).bind (run n) := by
  induction m generalizing σ with
  | zero => simp [run]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, run_succ, run_succ, Option.bind_assoc]
    congr 1; funext τ; exact ih τ

theorem orbit_eq_run (n : ℕ) : orbit n = run n initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (orbit n).bind step = _
    rw [ih, run_add n 1]
    congr 1; funext τ; simp [run]

/-- `P` holds at every state of the first `m` steps of the run from `σ` (indices `0 … m-1`). -/
def AllRun (P : State → Prop) (σ : State) (m : ℕ) : Prop :=
  ∀ i < m, ∀ τ, run i σ = some τ → P τ

theorem AllRun.add {P : State → Prop} {σ σ' : State} {m₁ m₂ : ℕ} (h₁ : AllRun P σ m₁)
    (h : run m₁ σ = some σ') (h₂ : AllRun P σ' m₂) : AllRun P σ (m₁ + m₂) := by
  intro i hi τ hτ
  by_cases hlt : i < m₁
  · exact h₁ i hlt τ hτ
  · obtain ⟨i', rfl⟩ : ∃ i', i = m₁ + i' := ⟨i - m₁, by omega⟩
    rw [run_add, h, Option.bind_some] at hτ
    exact h₂ i' (by omega) τ hτ

theorem AllRun.step' {P : State → Prop} {σ σ' : State} {m : ℕ} (hP : P σ)
    (h : step σ = some σ') (h₂ : AllRun P σ' m) : AllRun P σ (m + 1) := by
  rw [Nat.add_comm]
  refine AllRun.add (σ' := σ') ?_ (by simp [run, h]) h₂
  intro i hi τ hτ
  obtain rfl : i = 0 := by omega
  cases hτ; exact hP

theorem AllRun.mono {P Q : State → Prop} {σ : State} {m : ℕ} (h : AllRun P σ m)
    (hPQ : ∀ τ, P τ → Q τ) : AllRun Q σ m :=
  fun i hi τ hτ ↦ hPQ τ (h i hi τ hτ)

/-- Not a `k`-decrement firing state. -/
def NoFire (τ : State) : Prop := τ.pat = P1 → τ.a ≠ 9 ∧ τ.a ≠ 3

/-- **The B/S cascade**: `j` pairs from an odd `a + 12j` lower `a` by `12j` and raise `b` by `16j`,
with no firing on the way. -/
theorem cascade (k a b j : ℕ) (ha : a % 2 = 1) :
    run (2 * j) ⟨k, a + 12 * j, b, P1⟩ = some ⟨k, a, b + 16 * j, P1⟩ ∧
      AllRun NoFire ⟨k, a + 12 * j, b, P1⟩ (2 * j) := by
  induction j generalizing b with
  | zero =>
    refine ⟨by simp [run], fun i hi ↦ by omega⟩
  | succ j ih =>
    have h1 : step ⟨k, a + 12 * (j + 1), b, P1⟩ = some ⟨k, a + 12 * j + 3, b + 11, P1⟩ := by
      rw [step_B (s := ⟨k, a + 12 * (j + 1), b, P1⟩) rfl (by simp only; omega)
        (by simp only; omega)]
      simp only [Option.some.injEq, State.mk.injEq, and_true, true_and]; omega
    have h2 : step ⟨k, a + 12 * j + 3, b + 11, P1⟩ = some ⟨k, a + 12 * j, b + 16, P1⟩ := by
      rw [step_S (s := ⟨k, a + 12 * j + 3, b + 11, P1⟩) rfl (by simp only; omega)
        (by simp only; omega)]
      simp only [Option.some.injEq, State.mk.injEq, and_true, true_and]; omega
    obtain ⟨ih1, ih2⟩ := ih (b + 16)
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, run_succ, h1, Option.bind_some, run_succ,
        h2, Option.bind_some, ih1]
      simp only [Option.some.injEq, State.mk.injEq, and_true, true_and]; omega
    · have := AllRun.step' (P := NoFire) (fun _ ↦ by simp only; omega) h1
        (AllRun.step' (P := NoFire) (fun _ ↦ by simp only; omega) h2 ih2)
      rwa [show 2 * j + 1 + 1 = 2 * (j + 1) by ring] at this

theorem AllRun.zero (P : State → Prop) (σ : State) : AllRun P σ 0 := fun i hi ↦ by omega

/-- Tail bookkeeping: a run that steps `σ → σ₁ → …`. -/
theorem run_one {σ σ₁ : State} (h₁ : step σ = some σ₁) : run 1 σ = some σ₁ := by
  simp [run, h₁]

theorem run_two {σ σ₁ σ₂ : State} (h₁ : step σ = some σ₁) (h₂ : step σ₁ = some σ₂) :
    run 2 σ = some σ₂ := by
  simp [run, h₁, h₂]

theorem run_three {σ σ₁ σ₂ σ₃ : State} (h₁ : step σ = some σ₁) (h₂ : step σ₁ = some σ₂)
    (h₃ : step σ₂ = some σ₃) : run 3 σ = some σ₃ := by
  simp [run, h₁, h₂, h₃]

end Collatz.Bigfoot.V6

namespace Collatz.Bigfoot

open V6 Pat

/-- Ligocki's `(a, b, c)` as a V6 state. -/
def phi (s : Dyn) : V6.State := ⟨s.a, 2 * s.b - 1, 2 * s.c + 1, P1⟩

theorem phi_init : phi Dyn.init = V6.initial := rfl

/-- The firing states of the segment of `s` have `k = a` and come from `b ≡ 2, 5 (mod 6)`. -/
def SegFire (s : Dyn) (τ : V6.State) : Prop :=
  τ.pat = P1 → (τ.a = 9 ∨ τ.a = 3) → τ.k = s.a ∧ (s.b % 6 = 2 ∨ s.b % 6 = 5)

theorem SegFire.of_a {s : Dyn} {τ : V6.State} (h : τ.a ≠ 9 ∧ τ.a ≠ 3) : SegFire s τ :=
  fun _ h' ↦ by omega

theorem SegFire.of_P2 {s : Dyn} {τ : V6.State} (h : τ.pat = P2) : SegFire s τ :=
  fun h' ↦ by rw [h] at h'; cases h'

theorem SegFire.of_NoFire {s : Dyn} {τ : V6.State} (h : NoFire τ) : SegFire s τ :=
  fun hp h' ↦ by have := h hp; omega


/-- Closes `some ⟨…⟩ = some ⟨…⟩` goals between V6 states up to linear arithmetic. -/
macro "v6eq" : tactic =>
  `(tactic| (simp only [Option.some.injEq, State.mk.injEq, and_true, true_and, and_self] <;> omega))

/-- The segment's conclusion, for a fixed `s` and length `m`. -/
def SegOK (s : Dyn) (m : ℕ) : Prop :=
  AllRun (SegFire s) (phi s) m ∧
    (((s.b % 6 = 2 ∨ s.b % 6 = 5) → 1 ≤ s.a) →
      ∃ t, Dyn.step s = some t ∧ run m (phi s) = some (phi t))

theorem seg0 (A p c : ℕ) : SegOK ⟨A, 6 * p + 6, c⟩ (2 * p + 3) := by
  have hφ : phi ⟨A, 6 * p + 6, c⟩ = ⟨A, 11 + 12 * p, 2 * c + 1, P1⟩ := by
    simp only [phi]; v6eq
  obtain ⟨hc1, hc2⟩ := cascade A 11 (2 * c + 1) p rfl
  set B := 2 * c + 1 + 16 * p with hB
  have h1 : step ⟨A, 11, B, P1⟩ = some ⟨A, 2, B + 11, P1⟩ :=
    step_B (s := ⟨A, 11, B, P1⟩) rfl (by norm_num) (by norm_num)
  have h2 : step ⟨A, 2, B + 11, P1⟩ = some ⟨A, B + 15, 0, P1⟩ := step_W rfl rfl
  have h3 : step ⟨A, B + 15, 0, P1⟩ = some ⟨A, B + 12, 5, P1⟩ := by
    rw [step_S (s := ⟨A, B + 15, 0, P1⟩) rfl (by simp only; omega) (by simp only; omega)]; v6eq
  refine ⟨?_, fun _ ↦ ⟨⟨A, 8 * (p + 1) + c - 1, 2⟩, ?_, ?_⟩⟩
  · rw [hφ]
    refine AllRun.add (hc2.mono fun τ h ↦ SegFire.of_NoFire h) hc1 ?_
    refine AllRun.step' (SegFire.of_a (by simp)) h1 ?_
    refine AllRun.step' (SegFire.of_a (by simp)) h2 ?_
    exact AllRun.step' (SegFire.of_a (by simp only; omega)) h3 (AllRun.zero _ _)
  · simp only [Dyn.step]
    rw [if_pos (by omega)]
    congr 2; omega
  · rw [hφ, run_add, hc1, Option.bind_some, run_three h1 h2 h3]
    simp only [phi]; v6eq

theorem seg1 (A q c : ℕ) : SegOK ⟨A, 6 * q + 1, c⟩ (2 * q + 2) := by
  have hφ : phi ⟨A, 6 * q + 1, c⟩ = ⟨A, 1 + 12 * q, 2 * c + 1, P1⟩ := by
    simp only [phi]; v6eq
  obtain ⟨hc1, hc2⟩ := cascade A 1 (2 * c + 1) q rfl
  set B := 2 * c + 1 + 16 * q with hB
  have h1 : step ⟨A, 1, B, P1⟩ = some ⟨A + 1, B, 3, P2⟩ := step_Qkpp rfl rfl
  have h2 : step ⟨A + 1, B, 3, P2⟩ = some ⟨A + 1, B - 4, 7, P1⟩ := step_P2 rfl
  refine ⟨?_, fun _ ↦ ⟨⟨A + 1, 8 * q + c - 1, 3⟩, ?_, ?_⟩⟩
  · rw [hφ]
    refine AllRun.add (hc2.mono fun τ h ↦ SegFire.of_NoFire h) hc1 ?_
    refine AllRun.step' (SegFire.of_a (by simp)) h1 ?_
    exact AllRun.step' (SegFire.of_P2 rfl) h2 (AllRun.zero _ _)
  · simp only [Dyn.step]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2 <;> omega
  · rw [hφ, run_add, hc1, Option.bind_some, run_two h1 h2]
    simp only [phi]; v6eq

theorem seg2 (A q c : ℕ) : SegOK ⟨A, 6 * q + 2, c⟩ (2 * q + 2) := by
  have hφ : phi ⟨A, 6 * q + 2, c⟩ = ⟨A, 3 + 12 * q, 2 * c + 1, P1⟩ := by
    simp only [phi]; v6eq
  obtain ⟨hc1, hc2⟩ := cascade A 3 (2 * c + 1) q rfl
  set B := 2 * c + 1 + 16 * q with hB
  have h1 : step ⟨A, 3, B, P1⟩ = some ⟨A - 1, B + 7, 0, P1⟩ := step_DW rfl rfl
  have h2 : step ⟨A - 1, B + 7, 0, P1⟩ = some ⟨A - 1, B + 4, 5, P1⟩ := by
    rw [step_S (s := ⟨A - 1, B + 7, 0, P1⟩) rfl (by simp only; omega) (by simp only; omega)]; v6eq
  refine ⟨?_, fun ha ↦ ⟨⟨A - 1, 8 * q + c + 3, 2⟩, ?_, ?_⟩⟩
  · rw [hφ]
    refine AllRun.add (hc2.mono fun τ h ↦ SegFire.of_NoFire h) hc1 ?_
    refine AllRun.step' (fun _ _ ↦ ⟨rfl, Or.inl (show (6 * q + 2) % 6 = 2 by omega)⟩) h1 ?_
    exact AllRun.step' (SegFire.of_a (by simp only; omega)) h2 (AllRun.zero _ _)
  · have ha' : 1 ≤ A := ha (Or.inl (show (6 * q + 2) % 6 = 2 by omega))
    simp only [Dyn.step]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    congr 2; omega
  · rw [hφ, run_add, hc1, Option.bind_some, run_two h1 h2]
    simp only [phi]; v6eq

theorem seg3 (A q c : ℕ) : SegOK ⟨A, 6 * q + 3, c⟩ (2 * q + 3) := by
  have hφ : phi ⟨A, 6 * q + 3, c⟩ = ⟨A, 5 + 12 * q, 2 * c + 1, P1⟩ := by
    simp only [phi]; v6eq
  obtain ⟨hc1, hc2⟩ := cascade A 5 (2 * c + 1) q rfl
  set B := 2 * c + 1 + 16 * q with hB
  have h1 : step ⟨A, 5, B, P1⟩ = some ⟨A, B + 7, 2, P2⟩ := step_Qsame rfl rfl
  have h2 : step ⟨A, B + 7, 2, P2⟩ = some ⟨A, B + 3, 6, P1⟩ := by
    rw [step_P2 (s := ⟨A, B + 7, 2, P2⟩) rfl]; v6eq
  have h3 : step ⟨A, B + 3, 6, P1⟩ = some ⟨A, B, 11, P1⟩ := by
    rw [step_S (s := ⟨A, B + 3, 6, P1⟩) rfl (by simp only; omega) (by simp only; omega)]; v6eq
  refine ⟨?_, fun _ ↦ ⟨⟨A, 8 * q + c + 1, 5⟩, ?_, ?_⟩⟩
  · rw [hφ]
    refine AllRun.add (hc2.mono fun τ h ↦ SegFire.of_NoFire h) hc1 ?_
    refine AllRun.step' (SegFire.of_a (by simp)) h1 ?_
    refine AllRun.step' (SegFire.of_P2 rfl) h2 ?_
    exact AllRun.step' (SegFire.of_a (by simp only; omega)) h3 (AllRun.zero _ _)
  · simp only [Dyn.step]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    congr 2; omega
  · rw [hφ, run_add, hc1, Option.bind_some, run_three h1 h2 h3]
    simp only [phi]; v6eq

theorem seg4 (A q c : ℕ) : SegOK ⟨A, 6 * q + 4, c⟩ (2 * q + 2) := by
  have hφ : phi ⟨A, 6 * q + 4, c⟩ = ⟨A, 7 + 12 * q, 2 * c + 1, P1⟩ := by
    simp only [phi]; v6eq
  obtain ⟨hc1, hc2⟩ := cascade A 7 (2 * c + 1) q rfl
  set B := 2 * c + 1 + 16 * q with hB
  have h1 : step ⟨A, 7, B, P1⟩ = some ⟨A + 1, B + 7, 0, P1⟩ := step_QW rfl rfl
  have h2 : step ⟨A + 1, B + 7, 0, P1⟩ = some ⟨A + 1, B + 4, 5, P1⟩ := by
    rw [step_S (s := ⟨A + 1, B + 7, 0, P1⟩) rfl (by simp only; omega) (by simp only; omega)]; v6eq
  refine ⟨?_, fun _ ↦ ⟨⟨A + 1, 8 * q + c + 3, 2⟩, ?_, ?_⟩⟩
  · rw [hφ]
    refine AllRun.add (hc2.mono fun τ h ↦ SegFire.of_NoFire h) hc1 ?_
    refine AllRun.step' (SegFire.of_a (by simp)) h1 ?_
    exact AllRun.step' (SegFire.of_a (by simp only; omega)) h2 (AllRun.zero _ _)
  · simp only [Dyn.step]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    congr 2; omega
  · rw [hφ, run_add, hc1, Option.bind_some, run_two h1 h2]
    simp only [phi]; v6eq

theorem seg5 (A q c : ℕ) : SegOK ⟨A, 6 * q + 5, c⟩ (2 * q + 3) := by
  have hφ : phi ⟨A, 6 * q + 5, c⟩ = ⟨A, 9 + 12 * q, 2 * c + 1, P1⟩ := by
    simp only [phi]; v6eq
  obtain ⟨hc1, hc2⟩ := cascade A 9 (2 * c + 1) q rfl
  set B := 2 * c + 1 + 16 * q with hB
  have h1 : step ⟨A, 9, B, P1⟩ = some ⟨A - 1, 1, B + 12, P1⟩ := step_Bcoll rfl rfl
  have h2 : step ⟨A - 1, 1, B + 12, P1⟩ = some ⟨A - 1 + 1, B + 12, 3, P2⟩ := step_Qkpp rfl rfl
  have h3 : step ⟨A - 1 + 1, B + 12, 3, P2⟩ = some ⟨A - 1 + 1, B + 8, 7, P1⟩ := by
    rw [step_P2 (s := ⟨A - 1 + 1, B + 12, 3, P2⟩) rfl]; v6eq
  refine ⟨?_, fun ha ↦ ⟨⟨A, 8 * q + c + 5, 3⟩, ?_, ?_⟩⟩
  · rw [hφ]
    refine AllRun.add (hc2.mono fun τ h ↦ SegFire.of_NoFire h) hc1 ?_
    refine AllRun.step' (fun _ _ ↦ ⟨rfl, Or.inr (show (6 * q + 5) % 6 = 5 by omega)⟩) h1 ?_
    refine AllRun.step' (SegFire.of_a (by simp)) h2 ?_
    exact AllRun.step' (SegFire.of_P2 rfl) h3 (AllRun.zero _ _)
  · simp only [Dyn.step]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    congr 2; omega
  · have ha' : 1 ≤ A := ha (Or.inr (show (6 * q + 5) % 6 = 5 by omega))
    rw [hφ, run_add, hc1, Option.bind_some, run_three h1 h2 h3]
    simp only [phi]; v6eq

/-- **One `Dyn` step is one V6 segment.**  From `φ s` the V6 run reaches `φ (step s)` after `m ≥ 1`
steps (when the decrement inputs have `a ≥ 1`), and every firing state on the way satisfies
`SegFire s`.  Needs only `b ≥ 1` (true along the orbit, `Dyn.orbit_b_pos`). -/
theorem segment (s : Dyn) (hb : 1 ≤ s.b) : ∃ m, 1 ≤ m ∧ SegOK s m := by
  obtain ⟨A, b, c⟩ := s
  simp only at hb
  have h6 : b % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hdm : b = 6 * (b / 6) + b % 6 := (Nat.div_add_mod b 6).symm
  interval_cases hr : b % 6
  · obtain ⟨p, rfl⟩ : ∃ p, b = 6 * p + 6 := ⟨b / 6 - 1, by omega⟩
    exact ⟨_, by omega, seg0 A p c⟩
  · rw [hdm]; exact ⟨_, by omega, seg1 A (b / 6) c⟩
  · rw [hdm]; exact ⟨_, by omega, seg2 A (b / 6) c⟩
  · rw [hdm]; exact ⟨_, by omega, seg3 A (b / 6) c⟩
  · rw [hdm]; exact ⟨_, by omega, seg4 A (b / 6) c⟩
  · rw [hdm]; exact ⟨_, by omega, seg5 A (b / 6) c⟩

/-- In the segments of `b ≡ 2, 5 (mod 6)` a decrement firing state with `k = a` does occur. -/
theorem segment_fire (s : Dyn) (h : s.b % 6 = 2 ∨ s.b % 6 = 5) :
    ∃ i τ, run i (phi s) = some τ ∧ τ.pat = P1 ∧ (τ.a = 9 ∨ τ.a = 3) ∧ τ.k = s.a := by
  obtain ⟨A, b, c⟩ := s
  simp only at h ⊢
  rcases h with h | h
  · have hφ : phi ⟨A, b, c⟩ = ⟨A, 3 + 12 * (b / 6), 2 * c + 1, P1⟩ := by
      simp only [phi]; v6eq
    exact ⟨_, _, by rw [hφ]; exact (cascade A 3 (2 * c + 1) (b / 6) rfl).1, rfl, Or.inr rfl, rfl⟩
  · have hφ : phi ⟨A, b, c⟩ = ⟨A, 9 + 12 * (b / 6), 2 * c + 1, P1⟩ := by
      simp only [phi]; v6eq
    exact ⟨_, _, by rw [hφ]; exact (cascade A 9 (2 * c + 1) (b / 6) rfl).1, rfl, Or.inl rfl, rfl⟩

theorem Dyn.step_b_pos (s t : Dyn) (hc : 2 ≤ s.c) (h : Dyn.step s = some t) : 1 ≤ t.b := by
  obtain ⟨a, b, c⟩ := s
  simp only at hc
  dsimp only [Dyn.step] at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h) <;> subst h <;> simp only <;> omega

theorem Dyn.orbit_b_pos (n : ℕ) (s : Dyn) (h : Dyn.orbit n = some s) : 1 ≤ s.b := by
  match n, h with
  | 0, h => cases h; decide
  | n + 1, h =>
    obtain ⟨s', h', e⟩ := Dyn.orbit_succ _ _ h
    have := Dyn.orbit_c_mem n s' h'
    exact Dyn.step_b_pos s' s (by omega) e

theorem V6.orbit_add (M i : ℕ) (σ : V6.State) (h : V6.orbit M = some σ) :
    V6.orbit (M + i) = run i σ := by
  rw [V6.orbit_eq_run, run_add, ← V6.orbit_eq_run, h, Option.bind_some]

/-- **`KPosCascade` in Ligocki's coordinates**: the counter is at least `2` at every step with
`b ≡ 2` or `5 (mod 6)`. -/
def Margin2 : Prop :=
  ∀ n s, Dyn.orbit n = some s → (s.b % 6 = 2 ∨ s.b % 6 = 5) → 2 ≤ s.a

/-- `Margin2` implies Bigfoot's `Dyn` orbit never halts. -/
theorem margin2_nonhalt (h : Margin2) : ∀ n, Dyn.orbit n ≠ none := by
  intro n
  induction n with
  | zero => simp [Dyn.orbit]
  | succ n ih =>
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp ih
    intro hnone
    have hstep : Dyn.step s = none := by
      change (Dyn.orbit n).bind Dyn.step = none at hnone
      rwa [hs, Option.bind_some] at hnone
    obtain ⟨h2, h0⟩ := (Dyn.step_eq_none_iff' s).mp hstep
    have := h n s hs (Or.inl h2)
    omega

/-- **The repo's crux, decoded**: `KPosCascade ↔ Margin2`. -/
theorem kPosCascade_iff_margin2 : V6.KPosCascade ↔ Margin2 := by
  constructor
  · intro hK
    have fire : ∀ M s, V6.orbit M = some (phi s) → (s.b % 6 = 2 ∨ s.b % 6 = 5) → 2 ≤ s.a := by
      intro M s hM hr
      obtain ⟨i, τ, hτ, hp, h93, hk⟩ := segment_fire s hr
      rw [← V6.orbit_add M i _ hM] at hτ
      rw [← hk]
      rcases h93 with h9 | h3
      · exact hK.1 _ _ hτ hp h9
      · exact hK.2 _ _ hτ hp h3
    have track : ∀ n, ∃ s M, Dyn.orbit n = some s ∧ V6.orbit M = some (phi s) := by
      intro n
      induction n with
      | zero => exact ⟨Dyn.init, 0, rfl, rfl⟩
      | succ n ih =>
        obtain ⟨s, M, hs, hM⟩ := ih
        obtain ⟨m, -, -, hex⟩ := segment s (Dyn.orbit_b_pos n s hs)
        obtain ⟨t, ht, hrun⟩ := hex fun hr ↦ by have := fire M s hM hr; omega
        refine ⟨t, M + m, ?_, ?_⟩
        · change (Dyn.orbit n).bind Dyn.step = _
          rw [hs, Option.bind_some, ht]
        · rw [V6.orbit_add M m _ hM, hrun]
    intro n s hs hr
    obtain ⟨s', M, hs', hM⟩ := track n
    rw [hs] at hs'
    cases hs'
    exact fire M s hM hr
  · intro hm
    have track : ∀ n, ∃ s M, Dyn.orbit n = some s ∧ V6.orbit M = some (phi s) ∧ n ≤ M ∧
        ∀ N < M, ∀ τ, V6.orbit N = some τ → τ.pat = P1 → (τ.a = 9 ∨ τ.a = 3) → 2 ≤ τ.k := by
      intro n
      induction n with
      | zero => exact ⟨Dyn.init, 0, rfl, rfl, le_refl _, fun N hN ↦ by omega⟩
      | succ n ih =>
        obtain ⟨s, M, hs, hM, hnM, hbelow⟩ := ih
        obtain ⟨m, hm1, hall, hex⟩ := segment s (Dyn.orbit_b_pos n s hs)
        obtain ⟨t, ht, hrun⟩ := hex fun hr ↦ by have := hm n s hs hr; omega
        refine ⟨t, M + m, ?_, ?_, by omega, ?_⟩
        · change (Dyn.orbit n).bind Dyn.step = _
          rw [hs, Option.bind_some, ht]
        · rw [V6.orbit_add M m _ hM, hrun]
        · intro N hN τ hτ hp h93
          by_cases hlt : N < M
          · exact hbelow N hlt τ hτ hp h93
          · obtain ⟨i, rfl⟩ : ∃ i, N = M + i := ⟨N - M, by omega⟩
            rw [V6.orbit_add M i _ hM] at hτ
            obtain ⟨hk, hr⟩ := hall i (by omega) τ hτ hp h93
            rw [hk]
            exact hm n s hs hr
    have key : ∀ N τ, V6.orbit N = some τ → τ.pat = P1 → (τ.a = 9 ∨ τ.a = 3) → 2 ≤ τ.k := by
      intro N τ hτ hp h93
      obtain ⟨s, M, -, -, hNM, hbelow⟩ := track (N + 1)
      exact hbelow N (by omega) τ hτ hp h93
    exact ⟨fun N τ hτ hp h9 ↦ key N τ hτ hp (Or.inl h9),
      fun N τ hτ hp h3 ↦ key N τ hτ hp (Or.inr h3)⟩

end Collatz.Bigfoot
