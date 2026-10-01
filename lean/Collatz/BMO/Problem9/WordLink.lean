/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.WordCheck
import Collatz.BMO.Problem9.TableBridge

/-!
# BMO #9, port of Rocq `Module WordLink` (BMO9.v lines 2126-2179, ccz181078)

Links kernel words to `Block` calls, and packages the finite word-length bound:
`Bound L r` says every trace of continuing kernels of level `≤ L` has length `≤ r`.
(Rocq `Bridge.*` here is the repo's `TableBridge.*`.)
-/

namespace BMO9.WordLink

open Table WordLibrary

theorem continuing_good (k : Kernel) (hk : Continuing k) : (TableBridge.kernel k.pair).Good := by
  obtain ⟨e, hb, -, -⟩ := hk
  exact TableBridge.kernel_good k.index _ (built_valid hb).1.2.1

theorem continuing_gain (k : Kernel) (hk : Continuing k) : (k.index : ℤ) < gain k := by
  obtain ⟨e, hb, -⟩ := hk
  exact TableBridge.kernel_gain _ _ _ (built_valid hb)

theorem lookup_action (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (e : ℤ)
    (hx : Sane k x) (hq : 1 ≤ q) (ho : Odd q) (hs : Separated k x s r)
    (hb : Built s (.two y e)) :
    Action ⟨s, y⟩ (left k q x + right k q x) (left k q x)
      (left k q (next x s r y) + right k q (next x s r y)) (left k q (next x s r y)) := by
  have hy : TablePair s y := (built_valid hb).1.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [gain]
    rw [values_sum, values_sum]; linarith [next_mass x s r y]
  · have := TableBridge.lookup_leading k q x s r y hx hq ho hs hy
    dsimp only
    linear_combination this
  · obtain ⟨-, ⟨t, ht⟩, HH⟩ := quotient_spec k q x s r hx hq ho hs
    refine ⟨t, ?_⟩
    dsimp only
    rw [← ht]; linear_combination HH

theorem action_block (k : Kernel) (S U S' U' : ℤ) (h : Action k S U S' U') :
    Block.call (TableBridge.kernel k.pair) S (2*S - U + 3) S' (2*S' - U' + 3) := by
  obtain ⟨hS, hU, -⟩ := h
  refine ⟨hS, ?_⟩
  simp only [TableBridge.kernel]
  simp only [gain] at hS
  linear_combination 2*2^k.pair.d*hS - hU

theorem trace_blocks (word : List Kernel) (S U : ℤ) (h : Trace word S U) :
    ∃ S' U', Block.Calls (word.map fun k ↦ TableBridge.kernel k.pair) S (2*S - U + 3)
      S' (2*S' - U' + 3) := by
  induction h with
  | nil S U => exact ⟨S, U, Block.Calls.nil _ _⟩
  | cons hstep _ ih =>
      obtain ⟨S', U', hb⟩ := ih
      exact ⟨S', U', Block.Calls.cons (action_block _ _ _ _ _ hstep) hb⟩

theorem trace_suffix (pre suf : List Kernel) (S U : ℤ) (h : Trace (pre ++ suf) S U) :
    ∃ S' U', Trace suf S' U' := by
  induction pre generalizing S U with
  | nil => exact ⟨S, U, h⟩
  | cons k pre ih =>
      cases h with
      | cons _ ht => exact ih _ _ ht

/-- Rocq `bound L r`: every trace of continuing kernels of level `≤ L` has length `≤ r`. -/
def Bound (L : ℕ) (r : ℤ) : Prop :=
  ∀ word S U, (∀ k ∈ word, Continuing k ∧ k.index ≤ L) → Trace word S U →
    (word.length : ℤ) ≤ r

theorem bound_nonnegative (L : ℕ) (r : ℤ) (h : Bound L r) : 0 ≤ r := by
  simpa using h [] 0 0 (by simp) (Trace.nil 0 0)

theorem bound_mono (L L' : ℕ) (r r' : ℤ) (hL : L' ≤ L) (hr : r ≤ r') (hb : Bound L r) :
    Bound L' r' := by
  intro word S U hall htrace
  have := hb word S U (fun k hk ↦ ⟨(hall k hk).1, (hall k hk).2.trans hL⟩) htrace
  omega

theorem base_bound : Bound 2048 6 := by
  intro word S U hall htrace
  have := WordCheck.F2 word S U hall htrace
  omega

end BMO9.WordLink
