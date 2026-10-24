# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-24, lap 10)

The complete copy-producing base-counter replication phase is now proved:

* `copyBlockThrough_reaches_repRet` strengthens the lap-9 theorem to preserve an arbitrary
  already-appended `P`/`d` output.  Each later copy therefore scans through earlier copies and is
  appended at the genuine first explicit or implicit blank.
* `repStart_reaches_repScan`, `goS_reaches_cpScan`, and
  `repRet_reaches_repScanConfig` verify the `REP_START/REP_FIRST`, `GO_S`, and return-to-base
  control paths, including the generated stay transition and the scan across used `B` counters.
* `repScanSucc_reaches` composes one complete base-counter/copy circuit while preserving the
  work prefix, marked source, previous output, and exact remaining represented blanks.
* `repScanAll_reaches` inducts through all remaining counters.  It proves that `n` counters append
  exactly `n` copies of `copiedBlock body`; the existential final blank count honestly covers the
  point where the finite right-half list gives way to implicit blanks.
* `repStart_reaches_repScanDone` packages the whole phase: a unary base of `n + 1` reserves one
  counter in `REP_FIRST` and produces exactly `n` copies before reaching the all-`B`
  `REP_SCAN` configuration.

The generated/frozen files and the three frozen statements in `Halts.lean` remain unchanged.  The
scoped target still has exactly one `sorry`, at `halts_of_wf`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/Sim.lean`
* `lake build Collatz.GoodsteinTM.Sim Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Sim --axioms GoodsteinTM.repStart_reaches_repScanDone`

All are green; the real gate ends `FORMALIZE-TIER GREEN`, reports only the intended
`halts_of_wf` proof debt, and gives exactly `[Classical.choice, Quot.sound, propext]` for the new
headline.

## Current blocker and next attack

The remaining crux begins at the all-`B` exit of the now-complete replication phase, followed by
the macro step, init, and headline.  Parent identification, leaf erasure, copy-block marking,
comparison-mark restoration, arbitrary repeated copying, and base-counter control are proved.

Next, in order:

1. Prove `REP_SCAN` on the left blank enters `REP_DONE`, then induct through all `B`s to restore
   the unary base.  Compose `RD_S/RD_Z` to restore `S` to `P` and `z` to `d`, entering `GO_CHOP`
   on the exact nonblank tape produced by `repStart_reaches_repScanDone`.
2. Specialize the generic body/output formula using `markedCopyBody`, identify the result with
   `treeCells (chop (b - 1) t)`, and package the deep macro step.
3. Close the depth-one/base-bump branch and macro step, then prove init and the headline.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
