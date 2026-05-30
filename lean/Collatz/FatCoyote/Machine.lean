import Collatz.BB

/-!
# Fat Coyote — BB(3,3) holdout 397

Notation: `1RB1LB2LC_1LA2RB1RB_---0LA2LA`.

```
       0      1      2
  A | 1RB    1LB    2LC
  B | 1LA    2RB    1RB
  C | ---    0LA    2LA
```

Named "Fat Coyote" on the bbchallenge Discord (LegionMammal): a wider-period
cousin of Wily Coyote (holdout 531/532). Probviously non-halting per the
standard exhaustive decider sweep (Andrew Ducharme, Feb-Mar 2026) which
returned empty. Not yet officially declared a Cryptid; closest open analogue
to Bigfoot in BB(3,3).

Empirical structure (`notes/14`, `notes/15`):

* Pure sweep PDA — 100% of macro-step edits are at the right boundary of
  the left-side stack; pushes and pops strictly alternate.
* Linear run-length growth at slope 0.5/cycle, R² ≥ 0.998 up to 2.5M
  macro-loops / 2227 sweep cycles.
* 12 head signatures observed, 7 dominant (98%+ of mass).
* Bounded factor complexity c(n) ≤ 22 on the irregular-side word.

What is *NOT* the structure (`notes/15`, refuting the over-call in `notes/14`):

* No clean Bigfoot-style (a, b, c) 3-counter reduction. Peak bootstrap word
  is 97% unique per cycle across 623 reversal snapshots, so the auxiliary
  state at peak reversals exceeds any finite parametric form.
* Calibrated case split: 15% Bigfoot-shaped / 40% bounded counter automaton
  / 35% strictly harder than Bigfoot / 10% other.

So the Lean scaffold here mirrors `Collatz.Holdout153` (TM + non-halt
hypothesis), *not* `Collatz.Bigfoot` (which has Dynamics, Encoding,
Reduction, Classification). A `Dynamics` file for Fat Coyote requires
either (a) the 10M-loop reversal-burn experiment to settle case 1 vs
case 2/3, or (b) an honest sweep-PDA-with-unbounded-auxiliary type that
doesn't claim a finite reduction we haven't earned.
-/

namespace Collatz.FatCoyote

open BB

/-- The Fat Coyote (holdout 397) transition function. -/
def machine : Machine := fun q s =>
  match q, s with
  | State.A, Sym.s0 => some ⟨State.B, Sym.s1, Dir.R⟩  -- 1RB
  | State.A, Sym.s1 => some ⟨State.B, Sym.s1, Dir.L⟩  -- 1LB
  | State.A, Sym.s2 => some ⟨State.C, Sym.s2, Dir.L⟩  -- 2LC
  | State.B, Sym.s0 => some ⟨State.A, Sym.s1, Dir.L⟩  -- 1LA
  | State.B, Sym.s1 => some ⟨State.B, Sym.s2, Dir.R⟩  -- 2RB
  | State.B, Sym.s2 => some ⟨State.B, Sym.s1, Dir.R⟩  -- 1RB
  | State.C, Sym.s0 => none                            -- ---
  | State.C, Sym.s1 => some ⟨State.A, Sym.s0, Dir.L⟩  -- 0LA
  | State.C, Sym.s2 => some ⟨State.A, Sym.s2, Dir.L⟩  -- 2LA

end Collatz.FatCoyote
