# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`. Operator plan: `GOODSTEIN-TM-NEXT.md`. Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-24, lap 11 review) — objective complete

The scoped Goodstein machine tree is sorry-free, and the public theorem
`GoodsteinTM.halts_of_wf` is kernel-checked with the intended trust base.

The review first found and repaired a load-bearing boundary-invariant gap: a completed deep chop
can leave one represented blank to the far left of the unary base. Successive deep chops therefore
cannot all satisfy the former unpadded configuration shape. `basePad` and `chopConfigPadded`
record that Boolean boundary state, and the restore/turnaround path now proves the exact padded
successor configuration. The complete `REP_SCAN` exit, `REP_DONE`, `RD_S`, `RD_Z`, and `GO_CHOP`
path is composed in `deepChop_reaches` and identified with executable `chop`.

The rest of the machine-to-mathematics bridge is also complete:

* `shallowChop_reaches` proves deletion of a final depth-one node, the `GSTEP_BUMP` base increment,
  and return to the next chop configuration.
* `singletonChop_halts` and `emptyChop_halts` prove the two terminal boundary shapes reach, or
  already expose, the intended undefined transition.
* `init_write_prefix`, `init_reaches_bumpBlank`, and `initial_reaches_chop` prove the initializer,
  the first base bump from 2 to 3, and entry into `CHOP_START` for every seed.
* `goodsteinBattle` couples the changing unary base with executable `chop`.
  `goodsteinBattle_terminates` transfers the already-proved arbitrary-schedule hydra termination
  theorem, while `reaches_goodsteinBattle_or_halts` realizes every finite battle prefix on the
  concrete table.
* `halts_from_chop` composes those results, `halts_of_wf_sim` adds initialization, and the frozen
  statement `halts_of_wf` now delegates to that theorem. Consequently `halt_four_halts` and
  `halt_sixteen_halts` close without separate proof debt.

The generated/frozen files `Machine.lean`, `Defs.lean`, `Table.lean`, and `Check.lean` are byte-for-
byte unchanged from scaffold commit `60cfb73`. The three theorem statements in `Halts.lean` are
unchanged; only the former `sorry` body of `halts_of_wf` was filled. No `native_decide`, new axiom,
or hidden proof debt was introduced. The untracked `CLAUDE.local.md` predates this track and remains
intentionally uncommitted.

## Verification

All of the following passed on this checkpoint:

* `lake env lean lean/Collatz/GoodsteinTM/Sim.lean`
* `lake build Collatz.GoodsteinTM.Halts` — 3016 jobs
* `lake build Collatz.GoodsteinTM.Check` — 3009 jobs
* `rg -n '\bsorry\b|admit|axiom ' lean/Collatz/GoodsteinTM` — no matches
* `git diff --exit-code 60cfb73 -- lean/Collatz/GoodsteinTM/{Machine,Defs,Table,Check}.lean`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Halts --axioms GoodsteinTM.halts_of_wf`

The real gate ends `FORMALIZE-TIER GREEN`; `#print axioms GoodsteinTM.halts_of_wf` reports exactly
`[Classical.choice, Quot.sound, propext]`.

## Current blocker and next attack

There is no remaining in-scope blocker or proof obligation. The host should accept the scoped
completion predicate. No stretch work was requested; the next action is integration/review outside
this autonomous lap, not another mathematical attack.
