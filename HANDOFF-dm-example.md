# Handoff: Dubickas–Mossinghoff example and floor conjugacy (2026-10-16)

## Status

The lane-4 kickoff `KICKOFF-2026-10-16-dm-example.md` is complete in its
prescribed order.  `lean/Collatz/Antihydra/AkiyamaDubickas.lean` is sorry-free,
contains no `native_decide`, axiom declaration, or heartbeat override, and has no
line over 100 characters.  No theorem statement or definition was changed.

## Concrete advance

The ordered checkpoints were committed separately:

1. `f456243` proves `dmStops_mono` directly from the stopping witness for the
   larger residue set.
2. `069afc2` proves `dmStops_zero_top_of_minWord_ne_maxWord`: for `q ≥ 3`,
   `{0, q - 1}` is contained in `(Finset.range q).erase 1`, whose stopping
   property follows from both directions of `dmStops_ne_zero_iff_ne_one`.
3. `5712233` proves `next_sub_eq_floorNext_sub` and `digit_sub_eq`.  The common
   crux is the quotient–remainder split for `y = x - (q - 1)`: if `y % q = 0`,
   then `x / q = y / q`; otherwise `x / q = y / q + 1`.
4. `265b8f8` proves `iterate_next_sub_eq` by induction, using
   `x ≤ (floorNext q)^[k] x` to preserve the translation's lower bound.
5. `3652f2e` formats the new section within the 100-column source gate.

## Verification actually run

- `lake env lean lean/Collatz/Antihydra/AkiyamaDubickas.lean` — clean, with no
  output.
- `~/personal/bin/lean-green ~/src/collatz-cryptid-dmexample --target
  Collatz.Antihydra.AkiyamaDubickas --axioms
  Collatz.Antihydra.AkiyamaDubickas.iterate_next_sub_eq --import Collatz` —
  `FORMALIZE-TIER GREEN`, 8706 jobs; the headline uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `~/personal/bin/lean-green ~/src/collatz-cryptid-dmexample` —
  `FORMALIZE-TIER GREEN`, 8778 jobs.  The five reported sorries are the
  pre-existing obligations in Tao, Korec, Bigfoot V6KPos (two), and Bigfoot
  Reduction, all outside this kickoff.
- `git diff --check` — clean.
- `rg -n '\bsorry\b|native_decide|maxHeartbeats|^axiom '
  lean/Collatz/Antihydra/AkiyamaDubickas.lean` — no matches.
- The 100-column audit reports no long lines.

Every theorem and private lemma in the file was checked in one source-file
invocation with `#print axioms`.  The exact results, grouped by axiom set, are:

- No axioms: `minWord_three_seven`.
- `propext` only: `maxDigit_ne_zero`, `maxNext_eq_next`.
- `propext`, `Quot.sound`: `digit_spec`, `maxDigit_spec`,
  `digit_succ_of_ne_zero`, `next_succ_of_digit_ne_zero`,
  `digit_succ_of_eq_zero`, `shift`, `avoidsZero_iff`,
  `minWord_eq_maxWord_iff`, `next_double_of_digit_ne_one`, `digit_add_of_le`,
  `next_add_of_digit_le`, `shift_add`, `minWord_shift_add`, `digit_mul_of_lt`,
  `next_mul_of_digit_lt`, `scale`, `minWord_scale`, `dvd_next_of_dvd_digit`,
  `next_sub_eq_floorNext_sub`, and `digit_sub_eq`.
- `propext`, `Classical.choice`, `Quot.sound`: `next_eq_ceil`,
  `digit_eq_zero_iff`, `digit_eq_top_iff`, `dmStops_ne_zero_iff_ne_one`,
  `digit_double_eq_one_iff`, `halving`, `dmStops_singleton`, `dmStops_empty`,
  `not_dmStops_range`, `digit_three_eq_one_iff`,
  `dmStops_ne_two_iff_ne_one`, `dm43_pair_iff`, `dm43_classification`,
  `dmStops_mono`, `dmStops_zero_top_of_minWord_ne_maxWord`, and
  `iterate_next_sub_eq`.

Thus every declaration stays within the required axiom allowlist.

## Blocker and next attack

There is no remaining blocker or in-scope proof obligation.  The host predicate
`sorry-free:lean/Collatz/Antihydra/AkiyamaDubickas.lean` is met, and lane 4 proves
both Dubickas–Mossinghoff's two-element example from Akiyama's conjecture and the
full translation conjugacy between the ceiling and floor orbits.

The pre-existing untracked `CLAUDE.local.md` was read as startup context and left
untouched.
