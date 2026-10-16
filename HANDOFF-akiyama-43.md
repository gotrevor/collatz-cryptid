# Handoff: whole base-`4/3` Dubickas classification (2026-10-16)

## Status

The lane-3 kickoff `KICKOFF-2026-10-16-akiyama-43.md` is complete in its prescribed
order.  `lean/Collatz/Antihydra/AkiyamaDubickas.lean` is sorry-free, contains no
`native_decide` or heartbeat override, has no line over 100 characters, and builds
without warnings.  No statement or definition was changed.

## Concrete advance

The seven ordered checkpoints were committed separately:

1. `4ff1cf3` proves `shift_add` and `minWord_shift_add` using uniqueness of the
   admissible digit below `q`.
2. `6e2b0b5` proves `scale` and `minWord_scale` by the analogous scaled-digit
   uniqueness argument.
3. `3713090` proves `dvd_next_of_dvd_digit` by coprime cancellation.
4. `80a699a` proves `dmStops_singleton`, `dmStops_empty`, and `not_dmStops_range`.
   The singleton crux is the exact identity
   `q^k (x_k + a) = (q+1)^k (x_0 + a)` followed by cancellation of coprime powers
   and the contradiction `q^(x_0+a) > x_0+a`.
5. `a32d4a8` proves `dmStops_ne_two_iff_ne_one`, including the odd-seed step into
   an even successor and the existing `halving` bridge.
6. `6d69d0f` proves `dm43_pair_iff` by exhausting the three two-element subsets of
   `range 3`.
7. `18ea5a6` proves `dm43_classification`; `5dd38b8` then makes the finite case split
   linter-clean without changing the argument.

## Verification actually run

- `lake env lean lean/Collatz/Antihydra/AkiyamaDubickas.lean` -- clean, with no
  output.
- `~/personal/bin/lean-green ~/src/collatz-cryptid-akiyama --target
  Collatz.Antihydra.AkiyamaDubickas --axioms
  Collatz.Antihydra.AkiyamaDubickas.dm43_classification --import Collatz` --
  `FORMALIZE-TIER GREEN`, 8706 jobs; the headline uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `~/personal/bin/lean-green ~/src/collatz-cryptid-akiyama` --
  `FORMALIZE-TIER GREEN`, 8778 jobs.  The five reported sorries are the pre-existing
  obligations in Tao, Korec, Bigfoot V6KPos (two), and Bigfoot Reduction, all outside
  this kickoff.
- `git diff --check` -- clean.
- `rg -n '\bsorry\b|native_decide|maxHeartbeats'
  lean/Collatz/Antihydra/AkiyamaDubickas.lean` -- no matches.
- The 100-column audit reports no long lines.

Every theorem and private lemma in the file was checked in one source-file invocation
with `#print axioms`.  The exact results, grouped by axiom set, are:

- No axioms: `minWord_three_seven`.
- `propext` only: `maxDigit_ne_zero`, `maxNext_eq_next`.
- `propext`, `Quot.sound`: `digit_spec`, `maxDigit_spec`,
  `digit_succ_of_ne_zero`, `next_succ_of_digit_ne_zero`, `digit_succ_of_eq_zero`,
  `shift`, `avoidsZero_iff`, `minWord_eq_maxWord_iff`,
  `next_double_of_digit_ne_one`, `digit_add_of_le`, `next_add_of_digit_le`,
  `shift_add`, `minWord_shift_add`, `digit_mul_of_lt`, `next_mul_of_digit_lt`,
  `scale`, `minWord_scale`, and `dvd_next_of_dvd_digit`.
- `propext`, `Classical.choice`, `Quot.sound`: `next_eq_ceil`,
  `digit_eq_zero_iff`, `digit_eq_top_iff`, `dmStops_ne_zero_iff_ne_one`,
  `digit_double_eq_one_iff`, `halving`, `dmStops_singleton`, `dmStops_empty`,
  `not_dmStops_range`, `digit_three_eq_one_iff`, `dmStops_ne_two_iff_ne_one`,
  `dm43_pair_iff`, and `dm43_classification`.

Thus every declaration stays within the required axiom allowlist.

## Blocker and next attack

There is no remaining blocker or in-scope proof obligation.  The host predicate
`sorry-free:lean/Collatz/Antihydra/AkiyamaDubickas.lean` is met, and lane 3 completes
the requested general shift/scale lemmas and the entire base-`4/3` classification.

The pre-existing untracked `CLAUDE.local.md` was read as startup context and left
untouched.
