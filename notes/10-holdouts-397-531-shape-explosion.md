# Holdouts 397 and 531 - Shape-Explosion Finding 🌪️

Follow-up to `05-bb33-holdout-survey.md`. Goal: figure out whether 397 and 531 admit a Bigfoot-style small parametric reduction, or whether they're shape-explosive like 153, or something else entirely.

**Result: they're *more* shape-explosive than 153.** No rule structure visible to Quick_Sim across any block size 2-6, recursive prover, or 100k loops. Quick_Sim's failure is structural, not a tuning problem.

## Setup

Ran `tools/sandbox/bb33_397_531_probe.py` - 16 Quick_Sim configurations per holdout:

```
default, recursive, rec_b{2,3,4,5,6}, rec_long (100k loops)
```

Then `tools/sandbox/bb33_shape_count.py` - counts distinct macro-shape signatures (block-types + head, counts stripped) in 500-loop verbose-simulator traces.

## Quick_Sim probe (rules proven)

| Machine | block 2 | block 3 | block 4 | block 5 | block 6 | rec_long (100k) |
|---|---|---|---|---|---|---|
| 397 | 0 | 0 | 0 | 0 | 0 | 0 |
| 531 | 0 | 0 | 0 | 0 | 0 | 0 |

Zero rules of any kind (Diff, Linear, Collatz, Exponential, General) across all 16 runs. **The prover never even attempts a proof** - the `Failed proofs` counter is also 0. That means no two stored configurations have matching macro-shape, so the prover doesn't find candidate rules to test.

Growth rates (Num Nonzeros at 100k loops, default block size):

| Machine | Nonzeros @ 20k | Nonzeros @ 100k | Growth |
|---|---|---|---|
| 397 | 1,601 | 7,788 | ~linear |
| 531 | 2,377 | 11,737 | ~linear |
| 153 (reference) | 797→2,067 @ 20k | (slow) | polynomial |
| Bigfoot (reference) | ~10^17 step count by 5k loops | exponential | exponential |

So 397 and 531 grow linearly in macro-loops (similar to 153 polynomial regime), but with **no rule structure**.

## Shape-signature analysis (block size 2)

| Machine | configs sampled | distinct shapes | ratio | top shape recurrence |
|---|---|---|---|---|
| **Bigfoot** | 501 | 144 | **28.7%** | top shape appears 10× |
| **153** | 501 | 158 | **31.5%** | top shape appears 18× |
| **531** | 501 | 480 | **95.8%** | top shapes appear 1-2× |
| **397** | 501 | 501 | **100%** | every shape unique |

**397 has zero shape recurrence.** Every macro-loop produces a structurally distinct tape (modulo counter values). This is a *more extreme* phenomenon than 153's shape-explosion, where ~158 shapes still cover 500 loops.

## Interpretation

Two distinct classes of BB(3,3) holdout dynamics emerge:

1. **Bigfoot / 153 class** - many shape repetitions, sweep-style dynamics. The prover finds rules for Bigfoot (2-7 rules) and 153 (16 rules) because the sweep returns to recognizable macro-configurations.

2. **397 / 531 class** - shape-explosive. Macro-shapes don't repeat. Quick_Sim's diff-rule approach can't apply. They're growing, non-halting (empirically), but without obvious finite-state macro structure.

This is a real distinction in the BB(3,3) cryptid taxonomy. Both 397 and 531 escaped detection by Shawn's blog (no public analysis) - now we know one reason: standard cryptid analysis techniques don't get traction on them.

## What 397 looks like (default block size)

Sample final config at 100k loops:
```
0000^inf 1222^1 2221^1 2222^1 2211^1 1221^1 2221^1 1122^1 2111^1 1122^1
1211^1 1122^1 1222^2 1111^1 (1211) B> 2022^2_575 2021^1 0000^inf
```

A growing `2022^N` block on the right (sweep target), but the leftward "fossil record" of 4-cell blocks (`1222`, `2221`, `2222`, ...) is *irregular*. Compare to Bigfoot's regular `01^a 21^b 11^c` triple-counter structure.

## What 531 looks like (default block size)

Sample at 100k loops:
```
00^inf 12^5_847 (12) C> 11^2 21^1 12^2 22^1 21^1 12^1 21^3 12^1 21^1 11^1
21^1 12^1 22^1 12^1 22^1 11^1 10^1 00^inf
```

A growing `12^N` block on the left, irregular `12/21/22/11/10` 2-cell macros on the right. The right-side blocks accumulate with no detectable pattern.

## Hypothesis (low confidence ~25%)

The right-side "junk" sequences for 397 and 531 may encode the **digits of an irrational quantity** (Sturmian-like) or a **slowly-mixing substitution system**. If true, halting would require a specific finite suffix to appear, which would never happen for an aperiodic word.

Testing this hypothesis would require:
- Extract the right-side block sequence as a symbolic word.
- Compute its complexity function (distinct factor counts as a function of length).
- Compare against Sturmian (n+1), substitution (polynomial), or fully random (exponential).

Not done. Possible next session.

## Reproducibility

All sim files cached in `sim/H397_*.txt`, `sim/H531_*.txt`. Run:

```bash
sandbox bb33_397_531_probe.py        # ~3 minutes wall clock
sandbox bb33_shape_count.py          # ~30 seconds
```

## Files

- `sim/H397_default.txt` through `H397_rec_long.txt` (8 files, ~16KB total)
- `sim/H531_default.txt` through `H531_rec_long.txt` (8 files, ~14KB total)
- `sim/397_bauto_trace.txt`, `sim/397_b2_trace.txt`, etc. - verbose-simulator traces
- `sim/531_bauto_trace.txt`, `sim/531_b2_trace.txt`, etc.

## Open questions

- Why does the block finder pick block size 2 for 397 when its natural macro is clearly size 4 (`0212`, `1222`, ...)? Maybe `bf-loops` default is too short. Worth trying `--bf-loops 100000`.
- Are 397 and 531 conjugate / related by symmetry? They have similar growth profiles and identical 0-rules behavior.
- Is the right-side sequence Sturmian? Substitutive? Random? (See hypothesis above.)
