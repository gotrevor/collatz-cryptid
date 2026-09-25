# 30 - BMO #9 first pass 🦫

The question is whether the published four-rule rewrite system, starting at the all-zero
stream, ever reaches the halt case `(1, 0, rest)`.  Source: the [BMO wiki](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad), §9.  The Discord BMO9 thread in
`data/discord/2026-09-23/` already discusses the sum-modulo-three invariant, the frequent
`[1, x, …]` cases with `x ≡ 1 (mod 3)`, and exceptions.  This pass does **not** claim those
observations as new.

## Exact reductions

`lean/Collatz/BMO/Problem9.lean` models finite-support streams as lists with implicit
trailing zeros.  `Nonhalting` states the open question.  The file proves:

- `step_halts_iff`: a configuration halts exactly when its first two entries are `(1, 0)`.
- `step_creates_halt_iff`: a live step creates that prefix exactly from a configuration
  whose first two entries are `(1, 2)`.
- `orbit_sum_mod`: every reachable live configuration has sum divisible by three.

The second fact isolates a precise reachability target: exclude `(1, 2, rest)` from the
orbit.  It does not make that target easier on its own.  In particular `[1, 2, 0]` has
sum divisible by three and steps to `[1, 0, 1, 1]`; the known sum invariant alone permits
an immediately fatal state.  The missing fact must constrain the **tail jointly with the
first two entries**.

## Reproducible finite probe

`tools/sandbox/bmo9_probe.py probe 1000000` follows the exact rewrite rules with implicit
zeros.  Its `test` subcommand runs `tests/test_bmo9_probe.py`, whose subprocess assertions
use hand-computed examples of each published branch.  The million-step prefix does not
halt or encounter `(1, 2, rest)`.  Among configurations beginning with `1`, the second
entry is `1 mod 3` in 986 cases, `0 mod 3` in 42, and `2 mod 3` in 44.  The first exception
is step 799, `(1, 74, 27, …)`, so the naive `1 mod 3` invariant fails on the actual orbit.
This is finite evidence only, not a bound on later steps.

## Source correction, 2026-09-25

BMO #9 was announced solved on September 24.  The inspectable artifact is
[`verify/BMO9.v`](https://github.com/ccz181078/busycoq/blob/605d26d30610615ebe09ec23fcea079d6ef6ef50/verify/BMO9.v) in ccz181078/busycoq, commit `605d26d`
(September 24).  The 3,819-line Rocq file ends with `TM1.nonhalt : ~halts tm c0`,
linking the rewrite dynamics to the named machine.  Our Lean file proves
preliminary facts, not nonhalting.

The proof compresses the four rewrite rules into even/odd `Prefix.Step` rules,
treating the infinite zero tail via `Prefix.Exec`.  Its main bridge,
`Prefix.single_returns`, reduces repeated progress from singleton states
`[3*j]` to returns of special dyadic words `G k q` to singleton states.
`CheckTable.base_structured` checks a structured table through index 65,536;
`WordCheck.F2` checks that a specified continuing-word trace has length at
most six.  `Closure.all_good` proves returns for all indices by induction once
`FinalBudget.budget` supplies quantitative bounds at large scales.
`TM1.nonhalt_of_returns` converts the singleton returns into an infinite
machine run.  The file contains no `Admitted`, `Axiom`, or `Parameter`
declaration; imported files and the complete Rocq build were not audited here.

A Lean contribution would port known mathematics.  The smallest honest unit
is the even/odd prefix semantics and singleton-return bridge, with a checked
correspondence to the existing four-rule Lean model.  The finite tables and
global bounds are the substantial remaining work.  The proposed tail
condition below had no evidence beyond a finite probe and is withdrawn.
