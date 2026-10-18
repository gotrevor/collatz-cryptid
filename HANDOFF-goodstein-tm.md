# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-18, lap 8)

The complete parent-search and erase prefix now reaches the replicate loop on the actual
well-formed tape:

* `parEnd_reaches_markEnd` crosses the explicit blank tail and erases the marked last node with
  the exact `a + 4` blank accounting.
* `unmarkStart_reaches_repStart` traverses an arbitrary copy-block prefix right-to-left, restores
  every `D`, changes `C` to `S`, and verifies the generated two-step stay move into `REP_START`.
* `eraseLeaf_reaches_repStart` packages the generic nonempty block whose last symbol is `d` or
  `D`.  `parentFound_reaches_repStart` specializes it to the real parent block, including the
  genuine split between an empty suffix (mark the parent's final `D`) and a nonempty suffix (mark
  the suffix's final `d`).
* `markedCopyTail` is the canonical marked forward encoding presented to `CP_SCAN`.
* `chopStart_reaches_repStart_of_wf` composes lap 7's rightmost-parent search with the erase phase:
  from the real `CHOP_START` configuration for `WF (s ++ [a + 2])`, it reaches `REP_START` with
  the prefix `p` left of the head and the exact marked parent-plus-suffix block to its right.

The generated/frozen files and the three frozen statements in `Halts.lean` remain unchanged.  The
scoped target still has exactly one `sorry`, at `halts_of_wf`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/Sim.lean`
* `lake build Collatz.GoodsteinTM.Sim Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Sim --axioms GoodsteinTM.chopStart_reaches_repStart_of_wf`

All are green; the real gate ends `FORMALIZE-TIER GREEN`, reports only the intended
`halts_of_wf` proof debt, and gives exactly `[Classical.choice, Quot.sound, propext]` for the new
headline.

## Current blocker and next attack

The remaining crux is the copy/replicate half of route item 3, followed by the macro step, init,
and headline.  Parent identification, leaf erasure, copy-block marking, and comparison-mark
restoration are complete.

Next, in order:

1. Prove the `CP_SCAN/CARRY_*/CP_RET` copy loop by induction on `markedCopyTail a u`.  The useful
   invariant has a processed prefix marked `s/p/e`, an unprocessed suffix ending in `z`, and one
   copied output prefix immediately before the blank tail.  The `z` case exits via `CARRY_DL` to
   `CP_END`.
2. Prove the
   `REP_*/GO_S/CP_END/CP_UNM/REP_RET` loop by induction on remaining unmarked base counters.
3. Compose `REP_DONE` and `RD_S/RD_Z` to obtain the executable `chop (b - 1) t` tape, then close
   the depth-one/base-bump branch and macro step.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
