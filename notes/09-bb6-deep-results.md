# BB(6) Deep Pass - Results 🌊

Processed **1,085** BB(6) holdouts. Second run with beefier decider settings to test the data-shape thesis from the shallow run.

## Decider lineup

| Decider | Settings | Timeout | Avg elapsed | Timed out |
|---|---|---|---|---|
| Quick_Sim | max-loops 50000, --recursive, --exp-linear-rules | 120 s | 1.39 s | 0 |
| CPS small | block 30, window 100, max-iters 20000, max-configs 50000 | 90 s | 0.68 s | 2 |
| CPS large | block 80, window 250, max-iters 10000, max-configs 50000 | 120 s | 1.55 s | 7 |
| CTL2 (b=2) | cutoff 10000, block 2, offset 0 | 20 s | 0.07 s | 0 |
| CTL2 (b=4) | cutoff 5000, block 4, offset 0 | 20 s | 0.07 s | 0 |
| CTL3 (b=2) | cutoff 10000, block 2, offset 0 | 20 s | 0.07 s | 0 |
| CTL3 (b=4) | cutoff 5000, block 4, offset 0 | 20 s | 0.07 s | 0 |

## Headline

- **Total decided by deep pass**: 0 / 1,085 (0.00%)
- **Newly decided vs shallow run**: 0
- **Decisions by decider:**

## Top 30 by Quick_Sim Collatz-rule count

Most accelerable structure - candidates for hand analysis.

| Rules | Nonzeros | Decided? | Classification | Machine |
|---:|---:|:---:|---|---|
| 2071 | 441 |  | Structural counter + chaotic e | `1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC` |
| 1649 | 357 |  | Structural counter + chaotic e | `1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---` |
| 1221 | 430 |  | Monotone list | `1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---` |
| 1135 | 309 |  | Monotone list | `1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC` |
| 879 | 1782 |  | Cubic Mess | `1RB0RE_0RC---_1LD0RA_0LA0LD_1LC1RF_1RC0RE` |
| 871 | -2 |  | Quadratic Mess | `1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE` |
| 805 | 994 |  | Cubic Mess | `1RB0RF_1LC0RD_0LD0LC_1RE0RF_0RB---_1LB1RA` |
| 674 | -2 |  | Bell-like | `1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA` |
| 651 | 922305522 |  | Quadratic Mess | `1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA` |
| 642 | 578143275 |  | Quadratic Mess | `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD` |
| 627 | 23374 |  | Quadratic Mess | `1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA` |
| 530 | 1192 |  | Cubic Mess | `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` |
| 503 | -2 |  | Bell-like | `1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---` |
| 494 | -2 |  | Chaotic Fractal Type 1 | `1RB0RA_1LC0LE_0LD0LB_1RA0LF_1LB0RD_1LD---` |
| 493 | -2 |  | Chaotic Fractal Type 1 | `1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_1RC---` |
| 470 | -2 |  | Bell-like | `1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE` |
| 470 | -2 |  | Bell-like | `1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD` |
| 448 | -2 |  | Chaotic Bell Class 2 | `1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB` |
| 428 | -2 |  | Bell-like | `1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA` |
| 420 | -2 |  | Chaotic Bell Class 2 | `1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC` |
| 405 | -2 |  | Bell-like | `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---` |
| 395 | -2 |  | Chaotic Fractal Type 1 | `1RB0LF_1RC0RA_0RD0RB_1LE0RF_1LB0LE_1LE---` |
| 377 | 3383053677 |  | Chaotic Fractal Type 1 | `1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_1LA---` |
| 340 | -2 |  | Chaotic Fractal Type 1 | `1RB0RE_0RC0RA_1LD1RE_1LA0LD_1RA0LF_1LD---` |
| 333 | 629057706 |  | Chaotic Fractal Type 1 | `1RB---_1LC0RA_1LD0LC_1RE0RF_0RB0RD_1RD0LB` |
| 309 | -2 |  | Quadratic Mess | `1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB` |
| 281 | 1570 |  | Cubic Mess | `1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB` |
| 278 | -2 |  | Chaotic Bell Class 2 | `1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB` |
| 272 | -2 |  | Chaotic Bell Class 2 | `1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA` |
| 271 | 286366889 |  | Chaotic Fractal Type 1 | `1RB0RA_1LC0LE_0LD0LB_1RA1LE_1LB0RF_1RA---` |

## Top 30 by tape nonzeros

| Nonzeros | Rules | Decided? | Classification | Machine |
|---:|---:|:---:|---|---|
| 3383053677 | 377 |  | Chaotic Fractal Type 1 | `1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_1LA---` |
| 981882022 | 57 |  | Bell-like | `1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA` |
| 972916088 | 50 |  | Bell-like | `1RB1LD_0LC1RC_1RA1RD_1LE0RB_---1LF_0LC0LA` |
| 922305522 | 651 |  | Quadratic Mess | `1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA` |
| 791762270 | 50 |  | Chaotic Ack-like Bell | `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---` |
| 694436175 | 47 |  | Bell-like | `1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB` |
| 629057706 | 333 |  | Chaotic Fractal Type 1 | `1RB---_1LC0RA_1LD0LC_1RE0RF_0RB0RD_1RD0LB` |
| 578143275 | 642 |  | Quadratic Mess | `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD` |
| 452550217 | 239 |  | Chaotic Fractal Type 1 | `1RB1LE_1RC0RB_1LD0LE_0LA0LC_1LC0RF_1RB---` |
| 286366889 | 271 |  | Chaotic Fractal Type 1 | `1RB0RA_1LC0LE_0LD0LB_1RA1LE_1LB0RF_1RA---` |
| 103604053 | 122 |  | Quadratic Mess | `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC` |
| 103604053 | 122 |  | Quadratic Mess | `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` |
| 76791925 | 183 |  | Chaotic Bell Class 2 | `1RB0LF_1LC1LA_1LD0LC_1RE1LB_0RB1RA_---0RD` |
| 72760703 | 246 |  | Chaotic Fractal Type 1 | `1RB0LF_1RC0RA_0RD0RB_1LE1RA_1LB0LE_1LE---` |
| 32275874 | 94 |  | Quadratic Mess | `1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB` |
| 16782760 | 104 |  | Quadratic Mess | `1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD` |
| 9671983 | 0 |  | Bell-like | `1RB1LC_1LA1LD_1LD0LC_0LE0RD_1RA1LF_1RC---` |
| 6640061 | 159 |  | Chaotic Fractal Type 1 | `1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC` |
| 6327134 | 239 |  | Chaotic Fractal Type 1 | `1RB0RA_1LC0LE_0LD0LB_1RA0LF_1LB0RD_0RC---` |
| 6211965 | 0 |  | Bell-like | `1RB1LF_1RC1LD_1LB1LE_1LE0LD_0LA0RE_1RD---` |
| 3574946 | 0 |  | Bell-like | `1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---` |
| 3147479 | 235 |  | Chaotic Fractal Type 1 | `1RB0LF_1RC0RB_1LD0LE_0LA0LC_1LC0RA_0RD---` |
| 2992334 | 155 |  | Chaotic Fractal Type 1 | `1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB` |
| 983668 | 110 |  | Quadratic Mess | `1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE` |
| 854857 | 1 |  | Skelet 1-like Class 1 | `1RB1LD_0RC---_1RD1LE_1RE0LA_1RF1RB_1LA0LD` |
| 854677 | 1 |  | Skelet 1-like Class 1 | `1RB0RC_1LC1RC_1LD0RB_1LA0LE_1LF---_1LC1RA` |
| 740160 | 9 |  | Bell-like | `1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD` |
| 497971 | 0 |  | Skelet 1-like Class 1 | `1RB0LD_1RC1RE_1LD0LA_1RB1LA_0RF---_1RA1LB` |
| 497169 | 0 |  | Skelet 1-like Class 1 | `1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD` |
| 378525 | 0 |  | Quadratic Mess | `1RB1RF_1LC0RA_---0LD_1RE1LD_0LF0LB_1RA1LE` |

## Method

- Input: same 1085 undecided BB(6) machines as shallow run.
- Tooling: same (Shawn Ligocki's deciders, Python 3.14).
- Driver: `~/personal/tools/sandbox/bb6_deep.py`, 12 workers, results in `~/src/collatz-cryptid/sim/bb6_deep_run/results.csv`.
- Lin_Recur dropped from the lineup - shallow run already ruled out cyclers, and bumping max-steps to 100M just burned the time budget without deciding anything.
- CPS expanded: small + large block variants with bigger config budgets. CTL2 / CTL3 added at two block sizes each.

## Caveat

Default settings for each decider plus block/window sweeps in CPS and CTL. Anything we decide here is a candidate *new non-halting proof* worth verifying carefully before claiming. The bbchallenge community has run far more exhaustive parameter sweeps than this; if our pass finds a decision the community already explored, the signal is weak. If our pass finds something they haven't tried at these exact settings, the signal is stronger.
