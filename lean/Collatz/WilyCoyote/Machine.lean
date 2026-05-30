import Collatz.BB

/-!
# Wily Coyote — BB(3,3) holdout 531

Notation: `1RB2LA1LA_2LA0RA2RC_---0LC2RA`.

```
       0      1      2
  A | 1RB    2LA    1LA
  B | 2LA    0RA    2RC
  C | ---    0LC    2RA
```

Named "Wily Coyote" on the bbchallenge Discord (LegionMammal); Fat Coyote
(holdout 397, `Collatz.FatCoyote`) is the wider-period cousin. Probviously
non-halting per the standard exhaustive decider sweep (Andrew Ducharme,
Feb-Mar 2026) which returned empty. Not officially declared a Cryptid.

## Equivalence to holdout 532

531 and 532 differ in **exactly one transition** (C reading 1):
531 has `0LC`, 532 has `1RB`. The equivalence 531 ≡ 532 is *implicitly
conditional* on the (C, 1) transition being unreachable from blank in
both machines — a reachability-invariant proof, same shape as
`Collatz.Bigfoot.V6KPos.InvB`. Per `claude/knowledge/core/projects/
collatz-cryptid.md`, the equivalence has a convincing argument but is
not Rocq-verified.

## Empirical structure (`notes/14`, `notes/20`)

Wily Coyote is a sweep PDA with structurally distinct dynamics from
Fat Coyote:

* **~60× higher reversal rate per loop** than 397. Average ~8.5 loops
  per push-pop cycle, vs 397's ~500. Reflects 531's bounded short stack
  (max word length 24-33 at 10M loops per `notes/13`).
* **9 head signatures** observed (vs 397's 12).
* **One dominant peak signature** (`<left A, cell=12>`) and **one
  dominant valley signature** (`<right A, cell=10>`) — much narrower
  than 397's six-signature spread.
* **LEFT bootstrap fully saturated at 1 word** across 11,694 sampled
  reversals (10M loops, sample rate 100). Per `notes/20`.
* **RIGHT bootstrap slowing but not saturated** at 4531 / 4102 distinct
  words at peaks / valleys (~35-39% unique, novelty ratio ~0.40).

LegionMammal had a near-complete statistical model of 531 (abandoned
with hurdles per the bbchallenge Discord); the structural details above
may overlap with that model — we have not compared.

## Scope of this Lean module

The scaffold here mirrors `Collatz.FatCoyote`: TM-level Machine + non-halt
Hypothesis + trivial `SweepPDA` realization. No refined dynamics: while
531 *looks* more amenable to a finite-state reduction than 397 (LEFT
saturated), settling whether the RIGHT bootstrap actually saturates is
still open — the 10M data shows slowing, not saturation.
-/

namespace Collatz.WilyCoyote

open BB

/-- The Wily Coyote (holdout 531) transition function. -/
def machine : Machine := fun q s =>
  match q, s with
  | State.A, Sym.s0 => some ⟨State.B, Sym.s1, Dir.R⟩  -- 1RB
  | State.A, Sym.s1 => some ⟨State.A, Sym.s2, Dir.L⟩  -- 2LA
  | State.A, Sym.s2 => some ⟨State.A, Sym.s1, Dir.L⟩  -- 1LA
  | State.B, Sym.s0 => some ⟨State.A, Sym.s2, Dir.L⟩  -- 2LA
  | State.B, Sym.s1 => some ⟨State.A, Sym.s0, Dir.R⟩  -- 0RA
  | State.B, Sym.s2 => some ⟨State.C, Sym.s2, Dir.R⟩  -- 2RC
  | State.C, Sym.s0 => none                            -- ---
  | State.C, Sym.s1 => some ⟨State.C, Sym.s0, Dir.L⟩  -- 0LC
  | State.C, Sym.s2 => some ⟨State.A, Sym.s2, Dir.R⟩  -- 2RA

end Collatz.WilyCoyote
