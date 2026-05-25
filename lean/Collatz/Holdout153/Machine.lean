import Collatz.BB

/-!
# Holdout 153 — bbchallenge BB(3,3) unsolved holdout

Notation: `1RB0LB0RC_2LC2LA1RA_1RA1LC---` (equivalent to holdout 758).

```
       0      1      2
  A | 1RB    0LB    0RC
  B | 2LC    2LA    1RA
  C | 1RA    1LC    ---
```

Quick_Sim auto-discovers **16 parametric rules** governing its accelerated
behaviour. See `notes/06-holdout153-rules.md`. No public parametric
reduction (analogue of Bigfoot's `A(a, b, c)`) exists.
-/

namespace Collatz.Holdout153

open BB

/-- The Holdout 153 transition function. -/
def machine : Machine := fun q s =>
  match q, s with
  | State.A, Sym.s0 => some ⟨State.B, Sym.s1, Dir.R⟩  -- 1RB
  | State.A, Sym.s1 => some ⟨State.B, Sym.s0, Dir.L⟩  -- 0LB
  | State.A, Sym.s2 => some ⟨State.C, Sym.s0, Dir.R⟩  -- 0RC
  | State.B, Sym.s0 => some ⟨State.C, Sym.s2, Dir.L⟩  -- 2LC
  | State.B, Sym.s1 => some ⟨State.A, Sym.s2, Dir.L⟩  -- 2LA
  | State.B, Sym.s2 => some ⟨State.A, Sym.s1, Dir.R⟩  -- 1RA
  | State.C, Sym.s0 => some ⟨State.A, Sym.s1, Dir.R⟩  -- 1RA
  | State.C, Sym.s1 => some ⟨State.C, Sym.s1, Dir.L⟩  -- 1LC
  | State.C, Sym.s2 => none                            -- ---

end Collatz.Holdout153
