/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.UniqueTable
import Collatz.BMO.Problem9.CheckTable

/-!
# BMO #9, port of Rocq `Module WordLibrary` (BMO9.v lines 1869-1960, ccz181078)

The library of continuing kernels of level `≤ 2048`, read off a checked bank of table rows,
and the arithmetic action of a kernel on the unknowns `(S, U)`.
-/

namespace BMO9.WordLibrary

open Table

/-- Rocq `kernel`: a table pair `pair` at level `index`. -/
structure Kernel where
  index : ℕ
  pair : Pair
  deriving DecidableEq, Repr

def gain (k : Kernel) : ℤ := k.pair.b + k.pair.c + 2

/-- Rocq `continuing`. -/
def Continuing (k : Kernel) : Prop :=
  ∃ e, Built k.index (.two k.pair e) ∧ 1 ≤ k.index ∧ even_head k.index k.pair = false

@[irreducible] def bank : List Entry := (CheckTable.bank_build 2048).getD []

theorem bank_checked : CheckTable.bank_build 2048 = some bank := by native_decide

theorem bank_valid : bank.length = 2049 ∧ CheckTable.BankOk bank :=
  CheckTable.bank_build_spec _ _ bank_checked

theorem row_complete (s : ℕ) (f : Entry) (hs : s ≤ 2048) (hf : Built s f) :
    CheckTable.lookup bank s = some f := by
  obtain ⟨hlen, hbank⟩ := bank_valid
  unfold CheckTable.lookup
  have hlt : s < bank.length := by omega
  rw [List.getElem?_eq_getElem hlt]
  rw [UniqueTable.built_unique hf _ (hbank s _ (List.getElem?_eq_getElem hlt))]

def collect : ℕ → List Entry → List Kernel
  | _, [] => []
  | k, f :: r =>
      let rest := collect (k+1) r
      match f with
      | .one _ _ => rest
      | .two x _ => if 1 ≤ k then (if even_head k x then rest else ⟨k, x⟩ :: rest) else rest

theorem collect_tail (k : ℕ) (f : Entry) (xs : List Entry) (z : Kernel)
    (h : z ∈ collect (k+1) xs) : z ∈ collect k (f :: xs) := by
  cases f with
  | one => exact h
  | two x e =>
      simp only [collect]
      split_ifs <;> simp [h]

theorem collect_complete (k : ℕ) (xs : List Entry) (i : ℕ) (x : Pair) (e : ℤ)
    (hget : xs[i]? = some (.two x e)) (hk : 1 ≤ k + i) (he : even_head (k+i) x = false) :
    (⟨k+i, x⟩ : Kernel) ∈ collect k xs := by
  induction xs generalizing k i with
  | nil => simp at hget
  | cons f xs ih =>
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        simp only [Nat.add_zero] at hk he ⊢
        simp [collect, hk, he]
      · apply collect_tail
        have := ih (k+1) i hget (by omega) (by rwa [show k+1+i = k+(i+1) by omega])
        rwa [show k+1+i = k+(i+1) by omega] at this

def library : List Kernel := collect 0 bank

theorem library_complete (k : Kernel) (hk : Continuing k) (hmax : k.index ≤ 2048) :
    k ∈ library := by
  obtain ⟨s, x⟩ := k
  obtain ⟨e, hb, hs, he⟩ := hk
  have hrow := row_complete s _ hmax hb
  unfold CheckTable.lookup at hrow
  have := collect_complete 0 bank s x e hrow (by simpa using hs) (by simpa using he)
  simpa [library] using this

/-- Rocq `action`: one kernel step `(S, U) ↦ (S', U')`. -/
def Action (k : Kernel) (S U S' U' : ℤ) : Prop :=
  S' = S + gain k ∧
  2^k.pair.d*U' = k.pair.p*(2*S - U + 3) + 2^k.pair.d*k.pair.b ∧
  ∃ t, 2*S - U + 3 = 2^k.index*(2*t+1)

/-- Rocq `trace`. -/
inductive Trace : List Kernel → ℤ → ℤ → Prop
  | nil (S U : ℤ) : Trace [] S U
  | cons {k r S U S' U'} : Action k S U S' U' → Trace r S' U' → Trace (k :: r) S U

end BMO9.WordLibrary
