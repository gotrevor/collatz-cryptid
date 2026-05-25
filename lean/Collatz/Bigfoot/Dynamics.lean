import Mathlib.Tactic

/-!
# Bigfoot's parametric reduction (Ligocki, October 2023)

Shawn proved that from step 69 onward Bigfoot's tape encodes a triple
`(a, b, c)` such that one "phase" of TM execution advances `(a, b, c)`
through the rules below. The encoding maps the TM tape's macro-block
structure to these three counters.

This file states the dynamics. The encoding (TM tape ↔ triple) is the
content of the unproved theorem in `Bigfoot/Hypothesis.lean`.

Source: https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html
-/

namespace Collatz.Bigfoot

/-- The (a, b, c) state of Bigfoot's reduction. -/
structure Dyn where
  a : ℕ
  b : ℕ
  c : ℕ
deriving DecidableEq, Inhabited, Repr

namespace Dyn

/-- One step of the parametric dynamics. Returns `none` on the halting
branch (`a = 0 ∧ b % 6 = 2`).

Rules (verbatim from Ligocki 2023):
```
A(a, 6k,   c) → A(a,   8k + c - 1, 2)
A(a, 6k+1, c) → A(a+1, 8k + c - 1, 3)
A(a, 6k+2, c) → A(a-1, 8k + c + 3, 2)    when a > 0
A(a, 6k+3, c) → A(a,   8k + c + 1, 5)
A(a, 6k+4, c) → A(a+1, 8k + c + 3, 2)
A(a, 6k+5, c) → A(a,   8k + c + 5, 3)
A(0, 6k+2, c) → Halt(16k + 2c + 7)       (the halting branch)
```

For `c ∈ {2, 3, 5}` the subtraction `c - 1` is well-defined in `ℕ`. The
invariant `c ∈ {2, 3, 5}` along reachable states is property of the
dynamics from the initial state, not enforced at the type level. -/
def step (d : Dyn) : Option Dyn :=
  let k := d.b / 6
  let r := d.b % 6
  if r = 0 then some ⟨d.a, 8 * k + d.c - 1, 2⟩
  else if r = 1 then some ⟨d.a + 1, 8 * k + d.c - 1, 3⟩
  else if r = 2 then
    if d.a = 0 then none
    else some ⟨d.a - 1, 8 * k + d.c + 3, 2⟩
  else if r = 3 then some ⟨d.a, 8 * k + d.c + 1, 5⟩
  else if r = 4 then some ⟨d.a + 1, 8 * k + d.c + 3, 2⟩
  else some ⟨d.a, 8 * k + d.c + 5, 3⟩  -- r = 5

/-- The dynamics' starting state. Per Ligocki, Bigfoot's tape matches
`A(2, 1, 2)` after 69 TM steps. -/
def init : Dyn := ⟨2, 1, 2⟩

/-- The forward orbit. `none` once the halting branch fires. -/
def orbit : ℕ → Option Dyn
  | 0 => some init
  | n + 1 => (orbit n).bind step

end Dyn

end Collatz.Bigfoot
