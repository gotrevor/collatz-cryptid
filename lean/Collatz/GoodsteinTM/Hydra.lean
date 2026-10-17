/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.GoodsteinTM.Defs
import Mathlib.Data.List.DropRight

/-!
# Hydra moves on level sequences

The work region of the Goodstein machine is the preorder level sequence of a rooted forest.  A
single core iteration removes its last node.  If that node has depth `k > 1`, it then appends `n`
copies of the pruned subtree rooted at the node's parent.

This file gives that mathematical operation independently of the Turing-machine table.  The suffix
`s.rtakeWhile (k ≤ ·)` consists of the nodes strictly after the last depth-`k - 1` node.  Thus the
block to copy is `(k - 1) :: s.rtakeWhile (k ≤ ·)`.
-/

namespace GoodsteinTM

private def LevelRel (a b : ℕ) : Prop := 1 ≤ b ∧ b ≤ a + 1

/-- The pruned subtree ending a prefix `s`, when the deleted leaf had depth `k`. -/
def parentBlock (s : List ℕ) (k : ℕ) : List ℕ :=
  (k - 1) :: s.rtakeWhile (k ≤ ·)

/-- One rightmost Kirby--Paris hydra move, with `n` fresh copies of the pruned subtree.

For a depth-one leaf there is no regrowth.  The empty list is already dead and is fixed only to
make the operation total; the machine never starts a chop from an empty work region. -/
def chop (n : ℕ) (t : List ℕ) : List ℕ :=
  match t.getLast? with
  | none => []
  | some k =>
      let s := t.dropLast
      if k = 1 then s else s ++ (List.replicate n (parentBlock s k)).flatten

@[simp] theorem chop_nil (n : ℕ) : chop n [] = [] := rfl

@[simp] theorem chop_singleton_one (n : ℕ) : chop n [1] = [] := by
  simp [chop]

@[simp] theorem chop_append_one (n : ℕ) (s : List ℕ) : chop n (s ++ [1]) = s := by
  simp [chop]

private theorem flatten_replicate_isChain {R : ℕ → ℕ → Prop} {b : List ℕ}
    (hb : b.IsChain R)
    (hjoin : ∀ x ∈ b.getLast?, ∀ y ∈ b.head?, R x y) :
    ∀ n, (List.replicate n b).flatten.IsChain R := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, List.isChain_append]
      refine ⟨hb, ih, ?_⟩
      intro x hx y hy
      have hn : y ∈ (List.replicate n b).flatten.head? → y ∈ b.head? := by
        cases n with
        | zero => simp
        | succ n => simpa using id
      exact hjoin x hx y (hn hy)

private theorem parentBlock_isChain {s : List ℕ} {k : ℕ}
    (ht : WF (s ++ [k])) (hk : k ≠ 1) :
    (parentBlock s k).IsChain LevelRel := by
  have hsne : s ≠ [] := by
    rintro rfl
    simp [WF] at ht
    omega
  have hchain_s : s.IsChain LevelRel := by
    exact ht.2.left_of_append
  have hlastk : LevelRel (s.getLast hsne) k :=
    ht.2.rel_getLast_head_of_append hsne (by simp)
  have hk2 : 2 ≤ k := by
    unfold LevelRel at hlastk
    omega
  let p := s.rdropWhile (k ≤ ·)
  let u := s.rtakeWhile (k ≤ ·)
  have hpu : p ++ u = s := by
    simpa [p, u] using List.rdropWhile_append_rtakeWhile (p := (k ≤ ·)) (l := s)
  have hpne : p ≠ [] := by
    intro hp
    have hall : ∀ x ∈ s, k ≤ x := by
      simpa [p] using (List.rdropWhile_eq_nil_iff.mp hp)
    have hhead_mem : s.head hsne ∈ s := List.head_mem hsne
    have hhead_one : s.head hsne = 1 := by
      have := ht.1
      rw [List.head?_append_of_ne_nil _ hsne, List.head?_eq_some_head hsne] at this
      simpa using this
    have := hall (s.head hsne) hhead_mem
    omega
  have hplast_lt : p.getLast hpne < k := by
    have h := List.rdropWhile_last_not (p := (k ≤ ·)) (l := s) hpne
    simpa [p] using h
  have hchain_pu : (p ++ u).IsChain LevelRel := hpu ▸ hchain_s
  have hparent : p.getLast hpne = k - 1 := by
    by_cases hu : u = []
    · have hps : p = s := by simpa [hu] using hpu
      have hlast : LevelRel (s.getLast hsne) k :=
        ht.2.rel_getLast_head_of_append hsne (by simp)
      have : p.getLast hpne = s.getLast hsne := List.getLast_congr hpne hsne hps
      rw [this]
      unfold LevelRel at hlast
      omega
    · have hboundary : LevelRel (p.getLast hpne) (u.head hu) :=
        hchain_pu.rel_getLast_head_of_append hpne hu
      have huk : k ≤ u.head hu := by
        have hmem : u.head hu ∈ u := List.head_mem hu
        have := List.mem_rtakeWhile_imp (p := (k ≤ ·)) (l := s) hmem
        simpa [u] using this
      unfold LevelRel at hboundary
      omega
  have huChain : u.IsChain LevelRel := hchain_pu.right_of_append
  unfold parentBlock
  rw [← hparent]
  apply huChain.cons
  intro y hy
  have hu : u ≠ [] := by grind
  rw [List.head?_eq_some_head hu] at hy
  simp only [Option.mem_some_iff] at hy
  subst y
  exact hchain_pu.rel_getLast_head_of_append hpne hu

private theorem parentBlock_mem_lower {s : List ℕ} {k x : ℕ} (hk : 1 ≤ k)
    (hx : x ∈ parentBlock s k) : k - 1 ≤ x := by
  simp only [parentBlock, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact le_rfl
  · have h := List.mem_rtakeWhile_imp (p := (k ≤ ·)) (l := s) hx
    simp only [decide_eq_true_eq] at h
    omega

/-- A hydra chop preserves the level-sequence well-formedness invariant. -/
theorem chop_preserves_wf (n : ℕ) (t : List ℕ) (ht : WF t) : WF (chop n t) := by
  induction t using List.reverseRecOn with
  | nil => simpa [chop, WF]
  | append_singleton s k =>
    by_cases hk : k = 1
    · subst k
      rw [chop_append_one]
      exact ⟨by
        by_cases hs : s = []
        · simp [hs]
        · have h := ht.1
          rw [List.head?_append_of_ne_nil _ hs] at h
          exact h,
        ht.2.left_of_append⟩
    · have hsne : s ≠ [] := by
        rintro rfl
        simp [WF] at ht
        omega
      have hk2 : 2 ≤ k := by
        have hlast : LevelRel (s.getLast hsne) k :=
          ht.2.rel_getLast_head_of_append hsne (by simp)
        unfold LevelRel at hlast
        omega
      let b := parentBlock s k
      have hbne : b ≠ [] := by simp [b, parentBlock]
      have hbchain : b.IsChain LevelRel := parentBlock_isChain ht hk
      have hbjoin : ∀ x ∈ b.getLast?, ∀ y ∈ b.head?, LevelRel x y := by
        intro x hx y hy
        have hxm : x ∈ b := List.mem_of_mem_getLast? hx
        have hym : y ∈ b := List.mem_of_mem_head? hy
        have hxlower : k - 1 ≤ x := parentBlock_mem_lower (by omega) (by simpa [b] using hxm)
        have hyEq : y = k - 1 := by
          symm
          simpa [b, parentBlock] using hy
        subst y
        unfold LevelRel
        omega
      have hcopies : (List.replicate n b).flatten.IsChain LevelRel :=
        flatten_replicate_isChain hbchain hbjoin n
      have hchain_s : s.IsChain LevelRel := ht.2.left_of_append
      have hboundary :
          ∀ x ∈ s.getLast?, ∀ y ∈ (List.replicate n b).flatten.head?, LevelRel x y := by
        intro x hx y hy
        cases n with
        | zero => simp at hy
        | succ n =>
          have hyb : y ∈ b.head? := by
            simpa using hy
          have hyEq : y = k - 1 := by
            symm
            simpa [b, parentBlock] using hyb
          subst y
          have hxEq : x = s.getLast hsne := by
            rw [List.getLast?_eq_getLast_of_ne_nil hsne] at hx
            simpa using hx.symm
          have hlast : LevelRel x k := by
            rw [hxEq]
            exact ht.2.rel_getLast_head_of_append hsne (by simp)
          unfold LevelRel
          unfold LevelRel at hlast
          omega
      rw [chop]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, List.dropLast_concat,
        if_neg hk]
      constructor
      · have h := ht.1
        rw [List.head?_append_of_ne_nil _ hsne] at h
        rw [List.head?_append_of_ne_nil _ hsne]
        exact h
      · exact hchain_s.append hcopies hboundary

/-! Ground-truth checks against `tools/goodstein_tm/check.py`. -/

example : chop 2 [1, 2] = [1, 1, 1] := by decide +kernel
example : chop 3 [1, 2, 3] = [1, 2, 2, 2, 2] := by decide +kernel
example : chop 2 [1, 2, 3, 3] = [1, 2, 3, 2, 3, 2, 3] := by decide +kernel
example : chop 2 [1, 2, 3, 2, 3] = [1, 2, 3, 2, 2, 2] := by decide +kernel

example : WF (chop 2 [1, 2, 3, 3]) := by decide +kernel
example : WF (chop 2 [1, 2, 3, 2, 3]) := by decide +kernel

end GoodsteinTM
