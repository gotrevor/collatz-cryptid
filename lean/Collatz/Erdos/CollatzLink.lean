import Collatz.Conjecture
import Collatz.Erdos.Conjecture

/-!
# Prop-level relationships between Collatz and Erdős

These are *statements* of possible relationships, packaged as `Prop`s.  We
do **not** prove any of them here; we don't know of a published proof of an
implication in either direction, and our current intuition is that none is
known.

If we ever find a proof of `CollatzImpliesErdos` or vice versa, it would not
resolve either conjecture, but would unify them structurally — a real
result.  More likely: we instead chip away at specific shared substructure
(e.g. constraints on iterates that touch both `3`-adic and `2`-adic content).

See `notes/22-erdos-collatz.md` for the math discussion.
-/

namespace Collatz.Erdos

open Collatz

/-- "Collatz ⇒ Erdős". Currently an open question. -/
def CollatzImpliesErdos : Prop :=
  Conjecture → ErdosConjecture

/-- "Erdős ⇒ Collatz". Currently an open question. -/
def ErdosImpliesCollatz : Prop :=
  ErdosConjecture → Conjecture

/-- The two conjectures are equivalent. Strictly stronger than either
direction; would unify the two open problems if proved. -/
def CollatzEquivErdos : Prop := Conjecture ↔ ErdosConjecture

end Collatz.Erdos
