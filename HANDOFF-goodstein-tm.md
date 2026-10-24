# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-24, lap 9)

The complete copy loop is now proved and specialized to the actual marked parent block:

* `copyCell_reaches` verifies one mark/carry/append/return circuit when the first blank is explicit;
  `copyCellImplicit_reaches` covers the genuine finite-list edge where copying has reached the
  implicit blank beyond the represented tape.  `copyCellBlanks_reaches` packages both cases.
* `copyBody_reaches` inducts through an arbitrary `P`/`d` source body while tracking the marked
  source, appended output, and exact remaining explicit-blank count.
* `copyFinal_reaches_cpUnm` verifies the special `z/y`, `CARRY_DL`, and `CP_END` exit, and
  `copyUnmark_reaches_repRet` restores every `p/e/s` mark.
* `copyBlock_reaches_repRet` is the complete
  `CP_SCAN/CARRY_*/CP_RET/CP_END/CP_UNM` loop: it preserves `[S] ++ body ++ [z]`, appends
  `[P] ++ body ++ [d]`, and enters `REP_RET`.
* `markedCopyTail_reaches_repRet` specializes that theorem to the canonical block produced by
  lap 8's parent-search/erase prefix.  `mem_markedCopyBody` proves the required `P`/`d` alphabet
  invariant from `treeCells`.

The generated/frozen files and the three frozen statements in `Halts.lean` remain unchanged.  The
scoped target still has exactly one `sorry`, at `halts_of_wf`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/Sim.lean`
* `lake build Collatz.GoodsteinTM.Sim Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Sim --axioms GoodsteinTM.markedCopyTail_reaches_repRet`

All are green; the real gate ends `FORMALIZE-TIER GREEN`, reports only the intended
`halts_of_wf` proof debt, and gives exactly `[Classical.choice, Quot.sound, propext]` for the new
headline.

## Current blocker and next attack

The remaining crux is the replicate/base-counter wrapper around the completed one-copy theorem,
followed by the macro step, init, and headline.  Parent identification, leaf erasure, copy-block
marking, comparison-mark restoration, and one complete copy are proved.

Next, in order:

1. Prove the `REP_START/REP_FIRST/REP_SCAN/GO_S` entry and `REP_RET` return, then induct on the
   remaining unmarked base counters using `markedCopyTail_reaches_repRet`.  Preserve the already
   appended copies immediately after the marked source block and use the theorem's explicit/implicit
   blank accounting rather than assuming arbitrary padding.
2. Compose `REP_DONE` and `RD_S/RD_Z` to restore the base and source markers and obtain the exact
   executable `chop (b - 1) t` tape.
3. Close the depth-one/base-bump branch and macro step, then prove init and the headline.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
