/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.WordRelation
import Collatz.BMO.Problem9.WordLibrary

/-!
# BMO #9, port of Rocq `Module WordCheck` (BMO9.v lines 1962-2124, ccz181078)

A finite search refuting traces of seven continuing kernels of level `≤ 2048`: no such
word of length `≥ 7` acts on any `(S, U)`.  The Rocq `Forall` over words is written
`∀ k ∈ word, _`, and the Rocq `every` is `List.all`.
-/

namespace BMO9.WordCheck

open WordArith WordRelation WordLibrary

structure State where
  rel : Option Relation
  P : ℤ
  Q : ℤ
  C : ℤ
  D : ℕ
  mass : ℤ
  deriving DecidableEq, Repr

def Invariant (z : State) (S0 U0 S U : ℤ) : Prop :=
  Odd z.Q ∧ 2^z.D*U = z.P*S0 + z.Q*U0 + z.C ∧ S = S0 + z.mass ∧ Optional z.rel S0 U0

def A (z : State) : ℤ := 2^(z.D+1) - z.P
def B (z : State) : ℤ := (2*z.mass + 3)*2^z.D - z.C

theorem head_identity (z : State) (S0 U0 S U : ℤ) (hz : Invariant z S0 U0 S U) :
    2^z.D*(2*S - U + 3) = A z*S0 - z.Q*U0 + B z := by
  obtain ⟨-, hU, hS, -⟩ := hz
  simp only [A, B, pow_succ]
  rw [hS]; linear_combination -hU

theorem condition_spec (z : State) (k : Kernel) (S0 U0 S U S' U' : ℤ)
    (hz : Invariant z S0 U0 S U) (hstep : Action k S U S' U') :
    div2 (z.D + k.index + 1) (z.Q*U0 - A z*S0 - (B z - 2^(z.D + k.index))) := by
  obtain ⟨-, -, t, ht⟩ := hstep
  have HH := head_identity _ _ _ _ _ hz
  rw [ht] at HH
  refine ⟨-t, ?_⟩
  rw [pow_succ, pow_add]
  linear_combination HH

def push (z : State) (k : Kernel) (r : Relation) : State :=
  ⟨some r, k.pair.p*A z, -k.pair.p*z.Q, k.pair.p*B z + k.pair.b*2^(z.D + k.pair.d),
    z.D + k.pair.d, z.mass + gain k⟩

theorem push_spec (z : State) (k : Kernel) (r : Relation) (S0 U0 S U S' U' : ℤ)
    (hz : Invariant z S0 U0 S U) (hp : Odd k.pair.p) (hstep : Action k S U S' U')
    (hr : Holds r S0 U0) : Invariant (push z k r) S0 U0 S' U' := by
  obtain ⟨hS', hU', -⟩ := hstep
  have HH := head_identity _ _ _ _ _ hz
  obtain ⟨hQ, -, hS, -⟩ := hz
  refine ⟨?_, ?_, ?_, hr⟩
  · simp only [push, neg_mul]; exact (hp.mul hQ).neg
  · simp only [push, pow_add]
    linear_combination 2^z.D*hU' + k.pair.p*HH
  · simp only [push]; rw [hS', hS]; ring

/-- The match of Rocq `single`, split off so proofs never unfold the concrete bank. -/
def single_entry (s : ℕ) : Option Table.Entry → List Kernel
  | some (.two x _) => if 1 ≤ s then (if Table.even_head s x then [] else [⟨s, x⟩]) else []
  | _ => []

def single (s : ℕ) : List Kernel := single_entry s (CheckTable.lookup WordLibrary.bank s)

theorem single_complete (k : Kernel) (hk : Continuing k) (hmax : k.index ≤ 2048) :
    k ∈ single k.index := by
  obtain ⟨e, hb, hs, he⟩ := hk
  rw [single, row_complete _ _ hmax hb]
  simp [single_entry, hs, he]

def choices (z : State) : List Kernel :=
  match z.rel with
  | none => library
  | some r =>
      let bound := cutoff r (A z) z.Q
      let v := order bound (residual r (A z) (B z) z.Q)
      if v < bound then single (v - z.D)
      else library.filter (fun k ↦ decide (bound ≤ z.D + k.index))

theorem choices_spec (z : State) (k : Kernel) (S0 U0 S U S' U' : ℤ)
    (hz : Invariant z S0 U0 S U) (hk : Continuing k) (hmax : k.index ≤ 2048)
    (hstep : Action k S U S' U') : k ∈ choices z := by
  obtain ⟨-, -, t, ht⟩ := hstep
  have HH := head_identity _ _ _ _ _ hz
  obtain ⟨-, -, -, hR⟩ := hz
  have HH' : A z*S0 - z.Q*U0 + B z = 2^(z.D + k.index)*(2*t+1) := by
    rw [← HH, ht, pow_add]; ring
  unfold choices
  cases hr : z.rel with
  | none => exact library_complete k hk hmax
  | some r =>
      rw [hr] at hR
      obtain ⟨he, hl⟩ := pruning_spec r (A z) (B z) z.Q S0 U0 z.D k.index t hR HH'
      dsimp only at he hl ⊢
      have hv := order_bound (cutoff r (A z) z.Q) (residual r (A z) (B z) z.Q)
      split_ifs with hvb
      · rw [← he hvb, Nat.add_sub_cancel]
        exact single_complete k hk hmax
      · rw [List.mem_filter]
        exact ⟨library_complete k hk hmax, decide_eq_true (hl (by omega))⟩

def advance (z : State) (k : Kernel) : Option State :=
  match add z.rel (A z) z.Q (B z - 2^(z.D + k.index)) (z.D + k.index + 1) with
  | some r => some (push z k r)
  | none => none

theorem advance_spec (z : State) (k : Kernel) (S0 U0 S U S' U' : ℤ)
    (hz : Invariant z S0 U0 S U) (hk : Continuing k) (hstep : Action k S U S' U') :
    ∃ z', advance z k = some z' ∧ Invariant z' S0 U0 S' U' := by
  obtain ⟨e, hbuilt, -, -⟩ := hk
  have hp : Odd k.pair.p := (Table.built_valid hbuilt).1.2.1.1.2.2.2.1
  have hcond := condition_spec z k S0 U0 S U S' U' hz hstep
  obtain ⟨r, hadd, hholds⟩ :=
    add_spec z.rel (A z) z.Q (B z - 2^(z.D + k.index)) (z.D + k.index + 1) S0 U0
      hz.2.2.2 hz.1 hcond
  exact ⟨push z k r, by simp [advance, hadd], push_spec _ _ _ _ _ _ _ _ _ hz hp hstep hholds⟩

def refute : ℕ → State → Bool
  | 0, _ => false
  | fuel+1, z => (choices z).all fun k ↦
      match advance z k with
      | none => true
      | some z' => refute fuel z'

theorem refute_spec (fuel : ℕ) (z : State) (S0 U0 S U : ℤ) (hz : Invariant z S0 U0 S U)
    (hcheck : refute fuel z = true) (word : List Kernel)
    (hall : ∀ k ∈ word, Continuing k ∧ k.index ≤ 2048) (htrace : Trace word S U) :
    word.length < fuel := by
  induction fuel generalizing z S U word with
  | zero => simp [refute] at hcheck
  | succ fuel ih =>
      cases htrace with
      | nil => simp
      | @cons k rest _ _ S1 U1 hstep htail =>
          obtain ⟨hk, hmax⟩ := hall k (by simp)
          have hin := choices_spec _ _ _ _ _ _ _ _ hz hk hmax hstep
          simp only [refute, List.all_eq_true] at hcheck
          have hnext := hcheck k hin
          obtain ⟨z', hadv, hz'⟩ := advance_spec _ _ _ _ _ _ _ _ hz hk hstep
          rw [hadv] at hnext
          have := ih z' S1 U1 hz' hnext rest (fun k hk ↦ hall k (by simp [hk])) htail
          simp only [List.length_cons]; omega

def initial : State := ⟨none, 0, 1, 0, 0, 0⟩

theorem initial_spec (S U : ℤ) : Invariant initial S U S U :=
  ⟨odd_one, by simp [initial], by simp [initial], trivial⟩

theorem finite_check : refute 7 initial = true := by native_decide

theorem F2 (word : List Kernel) (S U : ℤ) (hall : ∀ k ∈ word, Continuing k ∧ k.index ≤ 2048)
    (htrace : Trace word S U) : word.length ≤ 6 := by
  have := refute_spec _ _ _ _ _ _ (initial_spec S U) finite_check word hall htrace
  omega

theorem finite_bounds :
    library.all (fun k ↦ decide (k.pair.d ≤ 5) && decide (gain k ≤ 5472)) = true := by
  native_decide

theorem kernel_bounds (k : Kernel) (hk : Continuing k) (hmax : k.index ≤ 2048) :
    k.pair.d ≤ 5 ∧ gain k ≤ 5472 := by
  have := List.all_eq_true.1 finite_bounds k (library_complete k hk hmax)
  simpa using this

end BMO9.WordCheck
