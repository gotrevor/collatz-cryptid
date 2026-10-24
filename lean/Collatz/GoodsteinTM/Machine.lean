/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic

/-!
# A Turing-machine framework for the Goodstein machine

Each step reads, writes, moves and changes state at once (the bbchallenge convention), over any
state type `St` and symbol type `Sy`.  The blank is `default`.  A tape half is a plain list, nearest
cell first, and cells past its end are blank.  So two configurations can differ only by trailing
blanks and still mean the same tape.  The plain lists keep `decide` usable for the computed
checks in `Check.lean`.
-/

namespace GoodsteinTM

/-- Head movement. -/
inductive Dir
  | L
  | R
  deriving DecidableEq, Repr, Inhabited

/-- A configuration: the state, the tape left of the head (nearest first), the scanned cell, and the
tape right of the head (nearest first). -/
structure Cfg (St Sy : Type) where
  state : St
  left : List Sy
  head : Sy
  right : List Sy
  deriving DecidableEq, Repr

variable {St Sy : Type} [Inhabited Sy]

/-- Write `w`, move `d`, enter `q`. -/
def Cfg.move (c : Cfg St Sy) (w : Sy) (d : Dir) (q : St) : Cfg St Sy :=
  match d with
  | .L => ⟨q, c.left.tail, c.left.headD default, w :: c.right⟩
  | .R => ⟨q, w :: c.left, c.right.headD default, c.right.tail⟩

/-- One step of the machine `M`; `none` when `M` is undefined on the scanned (state, symbol). -/
def step (M : St → Sy → Option (Sy × Dir × St)) (c : Cfg St Sy) : Option (Cfg St Sy) :=
  (M c.state c.head).map fun r => c.move r.1 r.2.1 r.2.2

/-- `n` steps; `none` if the machine halts first. -/
def stepN (M : St → Sy → Option (Sy × Dir × St)) : ℕ → Cfg St Sy → Option (Cfg St Sy)
  | 0, c => some c
  | n + 1, c => (step M c).bind (stepN M n)

/-- `M` started at `c` reaches a configuration where it is undefined. -/
def Halts (M : St → Sy → Option (Sy × Dir × St)) (c : Cfg St Sy) : Prop :=
  ∃ n c', stepN M n c = some c' ∧ M c'.state c'.head = none

end GoodsteinTM
