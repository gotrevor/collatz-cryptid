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

## Next mathematical move

Study the **first-return map** on configurations whose first entry is `1`, with the
remainder of the stream retained.  The immediate target is a condition on the tail that
survives all four rules and rules out the second entry `2`.  Any candidate should be
tested against step 799 and the later `0/2 mod 3` exceptions before formalization.  A
condition only on the first two entries repeats the failed modular route; a condition
on the full reachable tail could supply the missing mechanism.
