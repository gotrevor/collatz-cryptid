# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-17, review lap 3)

Route item 1 (hydra termination) is complete in
`lean/Collatz/GoodsteinTM/HydraTree.lean`:

* `Tree.exists_forestLevelsAt` is a length-inductive parser/inverse for preorder level sequences;
  `exists_forestLevelsAt_of_wf` proves every machine `WF` sequence has a rose-forest model.
* `chop_append_forestLevelsAt_of_rightChop` handles arbitrary positive depth and prefix context,
  closing the `RightChop.deep` bridge that was open last lap.
* `chop_forestLevelsAt_of_rightStep` identifies every ordered tree step with executable `chop`;
  `chop_strict_tree_descent` packages a strict `TreeLt` witness for every nonempty `WF` chop.
* `rightStep_exists`, `rightBattle_encoding`, and `chopBattle_terminates` prove termination for
  every schedule of finite copy counts.  This is the concrete list-level consequence of the
  already proved `treeLt_wf` engine.

Route item 2 has begun in `lean/Collatz/GoodsteinTM/Sim.lean` with `treeCells`, `tapeCells`, and
`chopConfig b t j`; the parameter `j` makes the explicit trailing blank tail arbitrary as required
by the operator plan.  The review found and kernel-pinned the frozen theorem's empty-seed edge:
`WF []` holds, and `empty_halts` proves that its machine reaches the undefined
`CHOP_START`/`]` entry after 13 steps.  Thus later macro simulation may assume `t ≠ []` after
dispatching this theorem.  No generated/frozen file or frozen theorem statement changed;
`Halts.lean` only imports `Sim.lean`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/HydraTree.lean`
* `lake build Collatz.GoodsteinTM.Sim Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.HydraTree
  --import Collatz.GoodsteinTM.HydraTree --axioms GoodsteinTM.chopBattle_terminates`

All are green.  The focused axiom gate reports exactly
`[Classical.choice, Quot.sound, propext]`.  The scoped target still has exactly the intended
`halts_of_wf` `sorry`.

## Current blocker and next attack

The remaining crux is route items 3–6: prove that the fixed 51-state table implements each hydra
macro step, then compose those steps using `chopBattle_terminates`.

Next, in order:

1. In `Sim.lean`, define a small existential reachability relation over `stepN`; prove the
   `stepN` addition/composition lemmas once.
2. Prove the generic scan lemma from route item 3 with arbitrary `List.replicate j .blank` tail.
3. Use it first for `CHOP_FINDL`, then the compare/erase loops.  Keep exact step counts only where
   they simplify composition; the headline needs existence.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
