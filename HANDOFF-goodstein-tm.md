# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-18, lap 7)

The rightmost-parent search is now complete for the actual well-formed level sequence, closing the
crux left by lap 6:

* `exists_parent_split_of_wf` in `Hydra.lean` splits `s` at its rightmost depth-`k - 1` node when
  `WF (s ++ [k])` and `k > 1`, and proves every node in the following suffix has depth at least
  `k`.
* `treeCells_append` makes encoded segment composition explicit.
* `candidateSuffix_reaches_retry` uses `List.reverseRecOn` to traverse that suffix right-to-left.
  Each step applies `candidateRejectedThrough_reaches_retry`; its restored node is prepended to the
  middle segment, so the invariant reconstructs the original suffix in order.
* `chopStartThrough_reaches_parent` composes the entire rejected suffix with the final successful
  `compareParentThrough_reaches` branch.
* `chopStart_reaches_parent_of_wf` applies the semantic decomposition and proves the real
  `CHOP_START` tape reaches the canonical `PAR_END` configuration.  This theorem should be the
  entry point for the remaining erase/copy proof.

The generated/frozen files and the three frozen statements in `Halts.lean` remain unchanged.  The
scoped target still has exactly one `sorry`, at `halts_of_wf`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/Hydra.lean`
* `lake build Collatz.GoodsteinTM.Sim`
* `lake build Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Sim --axioms GoodsteinTM.chopStart_reaches_parent_of_wf`

All are green; the real gate ends `FORMALIZE-TIER GREEN`, reports only the intended
`halts_of_wf` proof debt, and gives exactly `[Classical.choice, Quot.sound, propext]` for the new
headline.

## Current blocker and next attack

The remaining crux is the rest of route items 3–6.  Parent identification and traversal are done;
the machine is now at `PAR_END` with the parent marked `C`, paired parent/leaf depth marks `D`, the
deleted leaf marked `T`, and every rejected suffix node restored.

Next, in order:

1. Prove `PAR_END/ERASE_L/MARK_END/UNMARK_S` reaches the canonical `REP_START` copy-block
   configuration.  `MARK_END` has one genuine case split: for an empty suffix it marks the last
   parent-depth `D`; for a nonempty suffix it marks the last `d` of `treeCells suffix`.  A useful
   common abstraction is a nonempty block body whose last cell is `.d` or `.D`, with all remaining
   `.D`s restored by `UNMARK_S`.
2. Prove the `CP_SCAN/CARRY_*/CP_RET` copy loop by induction on that marked block, then the
   `REP_*/GO_S/CP_END/CP_UNM/REP_RET` loop by induction on remaining unmarked base counters.
3. Compose `REP_DONE` and `RD_S/RD_Z` to obtain the executable `chop (b - 1) t` tape, then close
   the depth-one/base-bump branch and macro step.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
