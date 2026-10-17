# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-17, lap 4)

Route item 1 remains complete (`chopBattle_terminates`).  Route items 2–3 advanced substantially
in `lean/Collatz/GoodsteinTM/Sim.lean`:

* `stepN_add`, `Reaches`, `reaches_trans`, and `reaches_of_stepN` provide the compositional
  simulation interface requested by the previous handoff.
* `stepN_scanLeft` and `stepN_scanRight` prove the generic scan lemma in both directions for an
  arbitrary symbol run and arbitrary tape tails.
* `chopFind_reaches_candidate` proves the complete `CHOP_FINDL` loop, including its zero-mark
  boundary, for every generated machine core.
* `candidateFind_reaches_compare` proves the complete positive-depth `CAND_FIND` loop.
* `chopStart_reaches_candidate` composes `CHOP_START`, `CHOP_D1`, and `CHOP_FINDL` for every final
  depth at least two.  `chopStart_reaches_compare` then composes the first two search segments and
  reaches a canonical `CMP_C` configuration for any positive-depth candidate.

All statements quantify over arbitrary left/right tape context, so in particular they preserve
the operator plan's arbitrary explicit blank tail.  The generated/frozen files and the three
frozen statements in `Halts.lean` remain unchanged.  The scoped target still has exactly one
`sorry`, at `halts_of_wf`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/Sim.lean`
* `lake build Collatz.GoodsteinTM.Sim Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts`

All are green; the real gate ends `FORMALIZE-TIER GREEN` and reports only the intended
`halts_of_wf` proof debt.

## Current blocker and next attack

The remaining crux is the rest of route items 3–6.  The current front is the comparison loop that
starts at the canonical `CMP_C` configuration proved this lap.

Next, in order:

1. Prove one pairing iteration through `CMP_C/CMP_TOL/CMP_L/CMP_TOC`, parameterized by the
   already-marked `D` prefix.
2. Induct on candidate depth to split the comparison into: parent found (`CMP_CEXH/CMP_LCHK` to
   `PAR_END`) and candidate rejected (`CMP_L` to `NOTPARENT`, restore `D`/`C`, retry
   `CAND_FIND`).
3. Compose the parent-found branch with `PAR_END/ERASE_L/MARK_END/UNMARK_S` before beginning the
   copy loop.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
