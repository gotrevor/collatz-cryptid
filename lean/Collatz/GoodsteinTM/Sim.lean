/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.GoodsteinTM.HydraTree

/-!
# Tape encodings for the Goodstein machine simulation

The simulation is anchored at `CHOP_START`, with the head scanning the final cell of the encoded
tree and an arbitrary finite tail of explicit blanks to its right.  The empty tree is a genuine
edge case of the frozen headline theorem: it reaches `CHOP_START` on the right bracket and halts
immediately because that table entry is undefined.
-/

namespace GoodsteinTM

/-- The `P d^k` work-region encoding of a level sequence. -/
def treeCells (t : List ℕ) : List Sy :=
  t.flatMap fun k => .P :: List.replicate k .d

/-- The complete finite nonblank tape segment at the start of a chop. -/
def tapeCells (b : ℕ) (t : List ℕ) : List Sy :=
  List.replicate b .b ++ [.lb, .rb] ++ treeCells t

/-- Configuration entering `CHOP_START`.  `j` explicit blanks represent an arbitrary finite
portion of the infinite blank tail. -/
def chopConfig (b : ℕ) (t : List ℕ) (j : ℕ) : Cfg St Sy :=
  let tape := tapeCells b t
  ⟨.core .CHOP_START, tape.dropLast.reverse, tape.getLastD .blank,
    List.replicate j .blank⟩

theorem cellsOf_eq_tapeCells_two (t : List ℕ) : cellsOf t = tapeCells 2 t := by
  simp [cellsOf, tapeCells, treeCells]

/-- The empty well-formed seed reaches the undefined `CHOP_START`/`]` entry after 13 steps. -/
theorem empty_halts : Halts (machine (cellsOf [])) start := by
  refine ⟨13, chopConfig 3 [] 1, ?_, ?_⟩ <;> decide +kernel

end GoodsteinTM
