# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-18, lap 5)

Route item 1 remains complete (`chopBattle_terminates`).  Route item 3 now includes the complete
successful depth-comparison branch in `lean/Collatz/GoodsteinTM/Sim.lean`:

* `stepN_scanRightUntilRight` and `stepN_scanRightUntilLeft` extend the generic scan interface to
  possibly empty runs followed by a state-changing stop transition.
* `comparePair_reaches` proves one complete `CMP_C/CMP_TOL/CMP_L/CMP_TOC` pairing circuit with an
  arbitrary already-marked `D` prefix and arbitrary tape context.
* `comparePairs_reaches_exhausted` inducts the circuit over the whole positive candidate depth.
* `compareExhausted_reaches_parent` proves the `CMP_CEXH/CMP_LCHK` finish, and
  `compareParent_reaches` packages the semantic result: a candidate whose depth is exactly one
  below the final node reaches `PAR_END`.

All statements quantify over arbitrary left/right tape context, so in particular they preserve
the operator plan's arbitrary explicit blank tail.  The generated/frozen files and the three
frozen statements in `Halts.lean` remain unchanged.  The scoped target still has exactly one
`sorry`, at `halts_of_wf`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/Sim.lean`
* `lake build Collatz.GoodsteinTM.Sim Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Sim --axioms GoodsteinTM.compareParent_reaches`

All are green; the real gate ends `FORMALIZE-TIER GREEN` and reports only the intended
`halts_of_wf` proof debt.  The focused axiom gate reports exactly
`[Classical.choice, Quot.sound, propext]` for `compareParent_reaches`.

## Current blocker and next attack

The remaining crux is the rest of route items 3–6.  The current front is the comparison rejection
branch.  For a well-formed preorder level sequence, candidates rejected before the rightmost
parent are at least as deep as the final node; the successful `depth = finalDepth - 1` case is now
closed.

Next, in order:

1. Prove the candidate-rejected case: after pairing the entire last-node depth, `CMP_L` reads the
   first trailing blank and enters `NOTPARENT`.
2. Prove `NOTPARENT` restores all `D` marks to `d`, restores `C` to `P`, and returns to
   `CAND_FIND`; then induct over the rejected encoded node blocks until the rightmost parent.
3. Compose `compareParent_reaches` with `PAR_END/ERASE_L/MARK_END/UNMARK_S` to reach the canonical
   `REP_START` copy-block configuration.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
