/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.GoodsteinTM.Table

/-!
# The Goodstein machines

A seed is a rooted tree written as a level sequence: the depths of its nodes in preorder, with the
root's children at depth 1.  The machine for seed `t` writes `bb [ ] P d^k₁ P d^k₂ …` (base 2 in
unary, then each node `P` followed by its depth in unary), one `init` state per cell, and then runs
`coreTable`.  The seed `hered n` of the hereditary base-2 tree of `n` gives `halt_n.json`:
`[1, 2, 3]` for 4 and `[1, 2, 3, 4]` for 16.
-/

namespace GoodsteinTM

/-- The initial tape for seed `t`. -/
def cellsOf (t : List ℕ) : List Sy :=
  [.b, .b, .lb, .rb] ++ t.flatMap fun k => .P :: List.replicate k .d

/-- The machine that writes `cells` and then runs the core. -/
def machine (cells : List Sy) : St → Sy → Option (Sy × Dir × St)
  | .init i, .blank =>
    if i + 1 < cells.length then some (cells.getD i .blank, .R, .init (i + 1))
    else some (cells.getD i .blank, .L, .core .GSTEP_BUMP)
  | .init _, _ => none
  | .core c, x => coreTable c x

/-- Blank tape, state `init 0`. -/
def start : Cfg St Sy := ⟨.init 0, [], .blank, []⟩

/-- A level sequence of a rooted forest: it starts at depth 1, and each depth is at least 1 and at
most one more than the previous. -/
def WF (t : List ℕ) : Prop :=
  t.head?.all (· = 1) ∧ t.IsChain fun a b => 1 ≤ b ∧ b ≤ a + 1

instance (t : List ℕ) : Decidable (WF t) := by unfold WF; infer_instance

end GoodsteinTM
