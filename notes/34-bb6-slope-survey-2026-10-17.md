# 34. A slope survey of the 663 BB(6) holdouts (2026-10-17)

**Question.**  The Wythoff-family theorems in collatz-moonshot (`RESEARCH-2026-10-13-amusical-single-chain.md`
§§60-67) need a counter whose slope is an irrational algebraic integer.  Antihydra and Hydra have
slope `3/2`.  Does any current BB(6) holdout carry an irrational slope?

**Answer at this instrument's depth: no.**  Of the 663 machines in mxdys's list of 2026-10-16
(`wiki.bbchallenge.org/w/images/6/69/BB6_holdouts_663.txt`), 54 show a converged exponential growth
ratio, and every one is a rational number.

## Instrument

`tools/sandbox/bb6_slope_survey/batch.py` runs sligocki's Quick_Sim simulator (prover on, recursive,
auto block size; `sligocki/busy-beaver` at its 2026-10-17 HEAD) for 300k loops, at most 120 s per machine.  It
keeps the chain-tape configurations with the head at a tape edge, groups them by shape (the tape with
exponents stripped, plus state and direction), and records the ratio of the largest exponent
between consecutive occurrences of a shape (late half, exponents above 1000, rounded to 4 places).
The slope is the base whose powers produce the ratio clusters.

**Controls (red-then-green).**
- The first screen (tape-width record times, `slope_screen.py`) **failed** its control: it gives
  `λ ≈ 1.001` on both Antihydra and the Fibonacci-counter halter
  `1RB1RF_0LB1LC_1LD1LF_1RE0LA_---0RA_1RA0RD`.  Width records see polynomial tape growth, not the
  counter's base.  Discarded.
- Quick_Sim's own proven rules are inner-loop diff rules; they never state the counter-level
  recurrence, so the rule list is not a slope instrument either.
- The shape-return statistic passes both rational controls exactly.  Antihydra: every ratio on its
  four most frequent shapes is `1.5` (623/623).  Bigfoot (`1RB2RA1LC_2LC1RB2RB_---2LA1LA`): ratios
  `1.3333, 1.7778, 2.3704, 3.1605` = `(4/3)^1..4`.
- ⚠️ **No positive irrational control.**  The Fibonacci halter shows no converged ratio at this depth
  (13 occurrences of its best shape; its next overflow lies past 1.5e8 steps).  So the survey's
  sensitivity to an irrational slope is argued, not demonstrated: a multi-exponent linear map such as
  `(a, b) ↦ (a + b, a)` would give a max-exponent ratio converging to its Perron root, which the
  4-place clustering would show as a single cluster.

## Results

| Slope | Machines | Sheet class |
|---|---|---|
| 3/2 | 20 | 17 Bell-like, 2 Quadratic Mess, 1 Chaotic Ack-like Bell |
| 4/3 | 11 | Bell-like |
| 9/4 | 7 | Bell-like (likely `3/2` seen every second step) |
| 8/3 | 5 | Bell-like |
| 10/3 | 4 | Bell-like |
| 2 | 2 | Quadratic Mess |
| 31/10 | 1 | Bell-like: `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` (ratios `3.1, 9.61, 29.791, 92.3521`) |
| 17/16, 35/32, 9/8 | 4 | Mess classes: small clusters, probably slow polynomial growth; unverified |

Per-machine table: `tools/sandbox/bb6_slope_survey/slopes.csv`; raw output `b663.jsonl`.  The other
609 machines show no converged exponential ratio within 300k loops (polynomial growth, shapes that
do not recur, or 38 timeouts).  This survey says nothing about them.

**Byproducts for the Foils gate.**  The sheet's "similar to Antihydra" cryptid
`1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC` has slope `4/3`, Bigfoot's slope.  The 27 machines
at `3/2` or `9/4` are the pool where `Foils.lean`'s parity-steering argument (`q = 2`) should carry
over once each is put in the `Census` Hydra schema.
