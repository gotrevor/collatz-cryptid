# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-17, lap 2)

Route item 1 (hydra termination) has its complete abstract engine and the first two concrete
encoding seams in `lean/Collatz/GoodsteinTM/HydraTree.lean`:

* `Tree`, `Tree.levelsAt`, `Tree.forestLevelsAt`: the rose tree and its preorder level encoding;
* `TreeLt`, `treeLt_wf`: the recursive multiset/path order, proved well-founded via Mathlib's
  `Relation.CutExpand`;
* `TreeChop`/`TreeStep`: the permutation-invariant structural hydra move;
* `RightChop`/`RightStep`: the exact ordered rightmost specialization used by the machine;
* `rightStep_lt`, `rightBattle_terminates`: strict descent and termination for every sequence of
  rightmost tree moves;
* `chop_forestLevelsAt_root`: exact agreement with executable `chop` for a depth-one leaf;
* `chop_forestLevelsAt_grand`: exact agreement for the depth-two regrowth constructor.  This proof
  checks the important off-by-one: list `chop n` leaves `n + 1` pruned-parent copies in total.

`Halts.lean` imports the new module.  No frozen/generated file was changed.

## Verification

* `lake build Collatz.GoodsteinTM.HydraTree Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.HydraTree
  --import Collatz.GoodsteinTM.HydraTree --axioms GoodsteinTM.rightBattle_terminates`

All are green.  The axiom gate reports exactly `[Classical.choice, Quot.sound, propext]`.  The
target still has exactly the intended `halts_of_wf` `sorry`.

## Current blocker and next attack

Two bridge lemmas remain before executable `chop` inherits `rightBattle_terminates`:

1. Prove a prefix/context lemma for `chop`, then induct on `RightChop` to cover its `deep`
   constructor.  The root and `grand` base cases are already proved.
2. Define a right-to-left stack parser for a level sequence and prove that every `WF t` has
   `t = Tree.forestLevelsAt cs 1`.  The encoding-side lower-bound lemmas are already available as
   `Tree.mem_levelsAt_lower` and `Tree.mem_forestLevelsAt_lower`.

Then package a well-founded relation/measure on `WF` sequences and prove every nonempty
`chop n t` strictly descends.  Only after route item 1 is green should the next lap begin route item
2 (`Sim.lean`, tape encoding).

The worktree's untracked `CLAUDE.local.md` predates this track and is not to be committed.
