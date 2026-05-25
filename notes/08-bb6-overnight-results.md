# BB(6) Overnight Run — Results 🌙

Processed **1,085** BB(6) holdout machines (Status=empty in the bbchallenge community spreadsheet snapshot).

## Deciders run

| Decider | Settings | Timeout | Avg elapsed |
|---|---|---|---|
| Lin_Recur_Detect | max-steps 1e6 | 30 s | 1.31 s |
| Quick_Sim | max-loops 10000, recursive | 60 s | 0.26 s |
| CPS | block 30, window 60, max-iters 5000 | 60 s | 0.49 s |

## Headline

- **Newly decided by some decider**: 0 / 1,085
  - Lin_Recur translated-cycler: 0
  - Quick_Sim reached halt:      0
  - Quick_Sim proven infinite:    0
  - CPS closed:                   0
- **Timeouts**: lr=0  qs=0  cps=1

## Classification breakdown

| Classification | Count |
|---|---:|
| Shift-overflow counter | 279 |
| Skelet 1-like Class 1 | 106 |
| Unknown | 104 |
| Bell-like | 66 |
| Cubic Mess | 58 |
| Quadratic Mess | 53 |
| Bell eats counter | 47 |
| Shift-overflow bouncer counter | 40 |
| Bouncer + Chaotic Edge | 27 |
| Chaotic Bell Class 1 | 23 |
| Chaotic Fractal Type 1 | 22 |
| Chaotic Bell Class 3 | 22 |
| Shift-overflow structural counter | 19 |
| Spaghetti | 18 |
| Structural counter + chaotic edge | 17 |
| Monotone list | 17 |
| Counter Class 1 | 16 |
| Skelet 1-like Class 2 | 15 |
| Chaotic 1dCA-like in bouncer | 14 |
| Sync bouncer counter | 12 |
| Chaotic Bell Class 2 | 11 |
| Chaotic Ack-like Bell | 11 |
| Chaotic Fractal Others | 10 |
| Chaotic 1dCA-like in bell | 9 |
| Bouncer + Complex Counter | 8 |
| Skelet 17-like | 8 |
| Counter Class 2 | 7 |
| Counter Class 3 | 7 |
| Translated Counter | 6 |
| Chaotic Bell Class 4 | 6 |
| Quadratic Skelet 17-like | 6 |
| List merging | 6 |
| Structural counter + counter | 5 |
| Fractal in Bouncer | 5 |
| Counter Class 4 | 2 |
| Bouncer + Translated Counter | 2 |
| Structural counter + bouncer | 1 |

## Quick_Sim Collatz-rule distribution

How many parametric rules Quick_Sim proved during the bounded 10,000-loop run. More rules = richer accelerable structure.

| # rules | machines |
|---:|---:|
| 0 | 854 |
| 1 | 18 |
| 2 | 13 |
| 3 | 6 |
| 4 | 11 |
| 5 | 11 |
| 6 | 8 |
| 7 | 1 |
| 8 | 4 |
| 9 | 5 |
| 10 | 5 |
| 11 | 4 |
| 12 | 8 |
| 15 | 4 |
| 16 | 2 |
| 17 | 3 |
| 18 | 4 |
| 19 | 3 |
| 20 | 5 |
| 21 | 5 |
| 22 | 7 |
| 23 | 6 |
| 24 | 7 |
| 25 | 5 |
| 26 | 4 |
| 27 | 1 |
| 28 | 4 |
| 29 | 5 |
| 30 | 1 |
| 31 | 5 |
| 32 | 1 |
| 33 | 4 |
| 34 | 2 |
| 35 | 3 |
| 36 | 2 |
| 37 | 4 |
| 38 | 3 |
| 40 | 2 |
| 43 | 3 |
| 46 | 4 |
| 47 | 1 |
| 49 | 1 |
| 50 | 3 |
| 55 | 1 |
| 61 | 2 |
| 65 | 3 |
| 69 | 1 |
| 70 | 1 |
| 73 | 1 |
| 78 | 1 |
| 79 | 1 |
| 82 | 1 |
| 83 | 1 |
| 86 | 2 |
| 89 | 1 |
| 90 | 1 |
| 93 | 1 |
| 96 | 2 |
| 97 | 1 |
| 98 | 1 |
| 99 | 1 |
| 108 | 1 |
| 109 | 1 |
| 122 | 1 |
| 152 | 1 |
| 174 | 1 |
| 177 | 1 |
| 186 | 1 |
| 210 | 1 |
| 270 | 1 |
| 299 | 1 |

## Top 25 machines by Quick_Sim Collatz-rule count

The candidates most worth a *real* look — machines whose accelerable structure is richest:

| Rules | Nonzeros | Classification | Machine |
|---:|---:|---|---|
| 299 | 178 | Structural counter + chaotic e | `1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC` |
| 270 | 172 | Structural counter + chaotic e | `1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---` |
| 210 | 146 | Monotone list | `1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---` |
| 186 | 187 | Cubic Mess | `1RB0RE_0RC---_1LD0RA_0LA0LD_1LC1RF_1RC0RE` |
| 177 | 263 | Cubic Mess | `1RB0RF_1LC0RD_0LD0LC_1RE0RF_0RB---_1LB1RA` |
| 174 | 492092613 | Quadratic Mess | `1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE` |
| 152 | -2 | Bell-like | `1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA` |
| 122 | 188568 | Quadratic Mess | `1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA` |
| 109 | 225178 | Quadratic Mess | `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD` |
| 108 | 938 | Quadratic Mess | `1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA` |
| 99 | 30783 | Quadratic Mess | `1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB` |
| 98 | -2 | Bell-like | `1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---` |
| 97 | 120 | Monotone list | `1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC` |
| 96 | -2 | Bell-like | `1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE` |
| 96 | -2 | Bell-like | `1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD` |
| 93 | 292 | Cubic Mess | `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` |
| 90 | 424654 | Chaotic Fractal Type 1 | `1RB0RA_1LC0LE_0LD0LB_1RA0LF_1LB0RD_1LD---` |
| 89 | 338626 | Chaotic Fractal Type 1 | `1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_1RC---` |
| 86 | -2 | Bell-like | `1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC` |
| 86 | -2 | Bell-like | `1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA` |
| 83 | -2 | Bell-like | `1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---` |
| 82 | -2 | Bell-like | `1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---` |
| 79 | 89143 | Chaotic Bell Class 2 | `1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC` |
| 78 | 606498 | Chaotic Bell Class 2 | `1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB` |
| 73 | 328 | Cubic Mess | `1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB` |

## Top 25 machines by Quick_Sim tape nonzeros

Tape size after 10,000 prover loops — proxy for growth rate. Big = exponential-ish (Bigfoot family). Small = polynomial-or-slower (153-like family).

| Nonzeros | Rules | Classification | Machine |
|---:|---:|---|---|
| 7820643112 | 47 | Chaotic Bell Class 2 | `1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC` |
| 2749006586 | 10 | Quadratic Mess | `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` |
| 2544485087 | 70 | Bell-like | `1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---` |
| 2298655515 | 10 | Chaotic Ack-like Bell | `1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RD---` |
| 735100873 | 0 | Quadratic Mess | `1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE` |
| 607352394 | 4 | Quadratic Mess | `1RB0LC_1RC0LE_1LA1RD_0RC0RA_1LF1RE_---1LB` |
| 544361551 | 43 | Chaotic Bell Class 2 | `1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA` |
| 492092613 | 174 | Quadratic Mess | `1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE` |
| 178612420 | 0 | Quadratic Mess | `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE` |
| 119819571 | 8 | Quadratic Mess | `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD` |
| 78646499 | 1 | Quadratic Mess | `1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD` |
| 75571503 | 2 | Quadratic Mess | `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB` |
| 16321067 | 20 | Quadratic Mess | `1RB1LC_1LC0RD_0LE1LA_0RF1RA_1RD0LA_---0RB` |
| 16321067 | 20 | Quadratic Mess | `1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB` |
| 12955618 | 32 | Quadratic Mess | `1RB1LD_1LC1RE_1RA0LB_1LF1LA_0RB0RC_---0RE` |
| 4885321 | 0 | Quadratic Mess | `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---` |
| 3118052 | 35 | Bell-like | `1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RD0LB_1RA---` |
| 2927865 | 24 | Chaotic Bell Class 2 | `1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC` |
| 1246413 | 0 | Quadratic Mess | `1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---` |
| 639102 | 55 | Chaotic Fractal Type 1 | `1RB0RE_0RC0RA_1LD1RE_1LA0LD_1RA0LF_1LD---` |
| 606498 | 78 | Chaotic Bell Class 2 | `1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB` |
| 470906 | 40 | Quadratic Mess | `1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB` |
| 424654 | 90 | Chaotic Fractal Type 1 | `1RB0RA_1LC0LE_0LD0LB_1RA0LF_1LB0RD_1LD---` |
| 338626 | 89 | Chaotic Fractal Type 1 | `1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_1RC---` |
| 338224 | 35 | Quadratic Mess | `1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD` |

## Method

- Sources: BB(6) community spreadsheet (`1mMp8bAcTFT91j7azn72liX8NSTwc2E_ozKnOGTfRCfw`), pulled as CSV.
- Filtered to rows with empty `Status` column (truly undecided as of April 2026 snapshot).
- Tooling: `~/src/busy-beaver/Code/` (Shawn Ligocki's deciders), Python 3.14 in `~/.venvs/bb`.
- Driver: `~/personal/tools/sandbox/bb6_overnight.py`, 8 parallel workers, results streamed to `~/src/collatz-cryptid/sim/bb6_run/results.csv`.
- Each machine gets ~150 s budget total across three deciders.

## Caveat

Default decider settings + tight time budgets. These are the *holdouts* — machines that resisted strong community effort. Expecting our cursory pass to decide them would be naive. **Real value is the data shape**: which classes accelerate, which have rich rule structure, which are tape-quiet. That tells us where to direct a real follow-up.
