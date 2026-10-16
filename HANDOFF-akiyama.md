# Handoff: Akiyama–Dubickas equivalence (2026-10-16)

## Status

The kickoff `KICKOFF-2026-10-16-akiyama.md` is complete, in its prescribed order.
`lean/Collatz/Antihydra/AkiyamaDubickas.lean` is sorry-free, contains no
`native_decide` or heartbeat override, and has no line over 100 characters.  No theorem
statement or definition was changed.

## Concrete advance

The six ordered checkpoints were committed separately:

1. `51c78cf` proves `digit_spec`, `maxDigit_spec`, and `next_eq_ceil`.
2. `1731c05` proves `shift`, with local successor-digit and successor-orbit lemmas.
3. `c29e7ea` proves `avoidsZero_iff` by taking the least zero digit in the reverse
   direction.
4. `7a25675` proves `minWord_eq_maxWord_iff` by synchronizing the two orbits while the
   minimal digit is nonzero.
5. `62ba53c` proves `dmStops_ne_zero_iff_ne_one`, including the residue/digit bridges
   `0 ↔ 0` and `1 ↔ q - 1`.
6. `8fb3ddc` proves `halving` by synchronizing the base-`4/3` orbits of `2y` and `y`.

## Verification actually run

- `lake env lean lean/Collatz/Antihydra/AkiyamaDubickas.lean` — clean, with no warnings.
- `~/personal/bin/lean-green ~/src/collatz-cryptid-akiyama --target
  Collatz.Antihydra.AkiyamaDubickas` — `FORMALIZE-TIER GREEN`, 8706 jobs, no sorry
  declarations in the target.
- `~/personal/bin/lean-green ~/src/collatz-cryptid-akiyama` — `FORMALIZE-TIER GREEN`,
  8778 jobs.  The reported sorries are the five pre-existing obligations in Tao, Korec,
  Bigfoot V6KPos, and Bigfoot Reduction, all outside this kickoff.
- `git diff --check` — clean.
- `rg -n '\bsorry\b|native_decide|maxHeartbeats'
  lean/Collatz/Antihydra/AkiyamaDubickas.lean` — no matches.
- The 100-column audit reports no long lines.

Every theorem and private lemma in the file was checked in one source-file invocation with
`#print axioms`.  The exact results were:

- `minWord_three_seven`: no axioms.
- `maxDigit_ne_zero`, `maxNext_eq_next`: `propext` only.
- `digit_spec`, `maxDigit_spec`, `digit_succ_of_ne_zero`,
  `next_succ_of_digit_ne_zero`, `digit_succ_of_eq_zero`, `shift`, `avoidsZero_iff`,
  `minWord_eq_maxWord_iff`, `next_double_of_digit_ne_one`: `propext`, `Quot.sound`.
- `next_eq_ceil`, `digit_eq_zero_iff`, `digit_eq_top_iff`,
  `dmStops_ne_zero_iff_ne_one`, `digit_double_eq_one_iff`, `halving`: `propext`,
  `Classical.choice`, `Quot.sound`.

Thus every declaration stays within the expected axiom allowlist.

## Blocker and next attack

There is no remaining blocker or in-scope proof obligation.  The host predicate
`sorry-free:lean/Collatz/Antihydra/AkiyamaDubickas.lean` is met.  A later, explicitly
scoped project could formalize the real-expansion side of AFS Section 5; this file
deliberately claims only the minimal/maximal-word and Dubickas stopping equivalences.

The pre-existing untracked `CLAUDE.local.md` was read as startup context and left untouched.
