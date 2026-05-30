import Collatz.BB
import Collatz.BB.SideTape
import Collatz.BB.Multistep
import Collatz.BB.Tactics

open BB

namespace TestTactics

/-- BB33_494's machine. -/
def tm : Machine := fun q s =>
  match q, s with
  | State.A, Sym.s0 => some ⟨State.B, Sym.s1, Dir.R⟩
  | State.A, Sym.s1 => some ⟨State.A, Sym.s2, Dir.L⟩
  | State.A, Sym.s2 => some ⟨State.A, Sym.s0, Dir.L⟩
  | State.B, Sym.s0 => some ⟨State.C, Sym.s2, Dir.L⟩
  | State.B, Sym.s1 => none
  | State.B, Sym.s2 => some ⟨State.A, Sym.s2, Dir.R⟩
  | State.C, Sym.s0 => some ⟨State.A, Sym.s0, Dir.R⟩
  | State.C, Sym.s1 => some ⟨State.C, Sym.s2, Dir.R⟩
  | State.C, Sym.s2 => some ⟨State.C, Sym.s1, Dir.L⟩

-- Test 1: single step (works).
example (l r : Side) :
    (⟨State.C, Dir.R, l, Sym.s2 >> r⟩ : Cfg2) -[tm]->*
      ⟨State.C, Dir.L, l, Sym.s1 >> r⟩ := by
  tm_step

-- The first INDUCTIVE multistep port:
-- busycoq's `l2_r1`: state C, dir L, n s2's on left → after n steps, n s1's on right.
/-- Lean port of busycoq's `l2_r1`. -/
theorem l2_r1 (n : ℕ) (l r : Side) :
    (⟨State.C, Dir.L, repeatList [Sym.s2] n l, r⟩ : Cfg2) -[tm]->*
      ⟨State.C, Dir.L, l, repeatList [Sym.s1] n r⟩ := by
  induction n generalizing r with
  | zero =>
      simp only [Side.repeatList_zero]
      tm_finish
  | succ n ih =>
      rw [show repeatList [Sym.s2] (n + 1) l =
        Side.cons Sym.s2 (repeatList [Sym.s2] n l) from rfl]
      tm_step
      tm_follow (ih (Sym.s1 >> r))
      rw [Side.merge_1]
      tm_finish

/-- Lean port of busycoq's `r1_l2`. Symmetric to `l2_r1`. -/
theorem r1_l2 (n : ℕ) (l r : Side) :
    (⟨State.C, Dir.R, l, repeatList [Sym.s1] n r⟩ : Cfg2) -[tm]->*
      ⟨State.C, Dir.R, repeatList [Sym.s2] n l, r⟩ := by
  induction n generalizing l with
  | zero =>
      simp only [Side.repeatList_zero]
      tm_finish
  | succ n ih =>
      rw [show repeatList [Sym.s1] (n + 1) r =
        Side.cons Sym.s1 (repeatList [Sym.s1] n r) from rfl]
      tm_step
      tm_follow (ih (Sym.s2 >> l))
      rw [Side.merge_1]
      tm_finish

/-- Lean port of busycoq's `l2_r0`: state A, dir L, n s2's on left → n s0's on right. -/
theorem l2_r0 (n : ℕ) (l r : Side) :
    (⟨State.A, Dir.L, repeatList [Sym.s2] n l, r⟩ : Cfg2) -[tm]->*
      ⟨State.A, Dir.L, l, repeatList [Sym.s0] n r⟩ := by
  induction n generalizing r with
  | zero =>
      simp only [Side.repeatList_zero]
      tm_finish
  | succ n ih =>
      rw [show repeatList [Sym.s2] (n + 1) l =
        Side.cons Sym.s2 (repeatList [Sym.s2] n l) from rfl]
      tm_step
      tm_follow (ih (Sym.s0 >> r))
      rw [Side.merge_1]
      tm_finish

end TestTactics
