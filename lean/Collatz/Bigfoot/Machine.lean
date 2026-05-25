import Collatz.BB

/-!
# The Bigfoot Turing machine

bbchallenge id 829.  Notation: `1RB2RA1LC_2LC1RB2RB_---2LA1LA`.

```
       0      1      2
  A | 1RB    2RA    1LC
  B | 2LC    1RB    2RB
  C | ---    2LA    1LA
```

The Cryptid found by Shawn Ligocki in October 2023. Resolving BB(3,3)
requires deciding whether this machine halts on blank tape.
-/

namespace Collatz.Bigfoot

open BB

/-- The Bigfoot transition function. -/
def machine : Machine := fun q s =>
  match q, s with
  | State.A, Sym.s0 => some ⟨State.B, Sym.s1, Dir.R⟩  -- 1RB
  | State.A, Sym.s1 => some ⟨State.A, Sym.s2, Dir.R⟩  -- 2RA
  | State.A, Sym.s2 => some ⟨State.C, Sym.s1, Dir.L⟩  -- 1LC
  | State.B, Sym.s0 => some ⟨State.C, Sym.s2, Dir.L⟩  -- 2LC
  | State.B, Sym.s1 => some ⟨State.B, Sym.s1, Dir.R⟩  -- 1RB
  | State.B, Sym.s2 => some ⟨State.B, Sym.s2, Dir.R⟩  -- 2RB
  | State.C, Sym.s0 => none                            -- ---
  | State.C, Sym.s1 => some ⟨State.A, Sym.s2, Dir.L⟩  -- 2LA
  | State.C, Sym.s2 => some ⟨State.A, Sym.s1, Dir.L⟩  -- 1LA

end Collatz.Bigfoot
