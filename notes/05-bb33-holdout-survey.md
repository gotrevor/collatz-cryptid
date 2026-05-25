# BB(3,3) Holdout Survey 🦴

Goal: orient ourselves against the 4 remaining BB(3,3) holdouts using Shawn Ligocki's `busy-beaver` toolchain - the same codebase he used to analyze Bigfoot. Self-research before pinging Shawn.

## Setup

```bash
# Cloned to: ~/src/busy-beaver/
# Venv:      ~/.venvs/bb (Python 3.14, gmpy2, protobuf, etc.)
# Run with:  ~/.venvs/bb/bin/python ~/src/busy-beaver/Code/Quick_Sim.py [opts] <tm>
```

## The 4 holdouts

| # | bbchallenge notation | Public status |
|---|---|---|
| **829** | `1RB2RA1LC_2LC1RB2RB_---2LA1LA` | Bigfoot - Cryptid, deeply analyzed by Shawn |
| 397 | `1RB1LB2LC_1LA2RB1RB_---0LA2LA` | Unsolved, no public analysis surfaced |
| 153 ≡ 758 | `1RB0LB0RC_2LC2LA1RA_1RA1LC---` | Unsolved, no public analysis surfaced |
| 531 ≡ 532 | `1RB2LA1LA_2LA0RA2RC_---0LC2RA` | Unsolved, no public analysis surfaced |

## Quick_Sim probe (`--max-loops 5000`)

| # | Collatz rules found | Loop steps reached | Tape nonzeros | Tape copies |
|---|---|---|---|---|
| Bigfoot | 2 | ~10^17 | ~10^17 | 354 |
| **153** | **16** ⭐ | (slow) | 797 → 2,067 at 20k | 3,690 |
| 397 | 0 | (linear) | 435 | 0 |
| 531 | 0 | (linear) | 616 | 0 |

Interpretation:

- **Bigfoot** is the cryptid: Quick_Sim's proof system finds 2 macro-rules that accelerate it to 10^17 steps. Matches Shawn's known result.
- **153** is the highest-yield holdout *for our purposes*: the prover auto-discovers **16 Collatz-like parametric rules**. More than Bigfoot. The machine is growing slower than Bigfoot in raw step count, but its *structure* is the richest of the unsolved three.
- **397** and **531** stall the prover: 5,000 configurations stored, **zero rules proved**. The prover's default settings (block-size auto, no recursion) don't catch their dynamics. They're not obviously Collatz-like - might be polynomial-growth, might need exotic deciders, might just need different prover options.

## Lin_Recur (1M steps)

```
Lin_Recur Bigfoot:  no recurrence
Lin_Recur 397:      no recurrence
Lin_Recur 153:      no recurrence
Lin_Recur 531:      no recurrence
```

All 4 are confirmed non-cyclers within 1M steps. Expected - they wouldn't be holdouts otherwise.

## Holdout 153's auto-discovered rules

`--verbose-prover` output captured at `sim/153_verbose_full.txt`. 11 of 16 rules surfaced in 500 prover loops; the remaining 5 emerge later. Two families:

### Family A — "sweep" rules (Steps: 6, Loops: 2)

A state moves left across a block, consuming 2 symbols of one kind and emitting 2 of another. Linear bookkeeping. Examples:

```
Diff Rule 0:  10^(a+3) <B (02) 02^(b+1) 01 11 20    →   10^-2 ... 02^+2 ...
Diff Rule 2:  01^(f+3) <C (20) 20^(g+1)             →   01^-2 ... 20^+2
Diff Rule 6:  10^(u+3) <C (12) 02^(v+1)             →   10^-2 ... 02^+2
Diff Rule 7:  10^(z+3) <B (02) ... 11^(?) 12        →   10^-2 ... 02^+2 ...
```

The pattern: state sweeps left over a homogeneous block, the block shrinks by 2, a neighbor block grows by 2. **These are NOT Collatz - they're the "geological strata" that the sweep is moving through.**

### Family B — "expansion" rules (Steps: 8·param + 32, Loops: 8)

The actual Collatz-like rules. State moves through an internal `(11)` block of size `d+1`, taking **8·d + 32** machine steps:

```
Diff Rule 1:  10^(c+3) 11^(d+1) (11) B>  21 11^(e+2) 20  →  10^-2 11^+3 ... 11^-1 ...
Diff Rule 5:  01^(q+3) 11^(r+1) (11) A>  11^(s+2) 12     →  01^-2 11^+3 ... 11^-1 ...
Diff Rule 8:  10^(?)   11^(?)   (11) B>  21 11^(?)   12  →  10^-2 11^+3 ... 11^-1 ...
```

A `11^d`-block expands by 3 while its neighbor shrinks by some amount and the head transits. **Step count linear in `d`.** This is the Collatz signature - a "phase" whose duration scales with a state variable.

### Hypothesis (mine, low confidence ~40%)

Holdout 153's behavior is governed by a discrete dynamical system on *block sizes* — a tuple like `(α, β, γ, δ)` counting the four block types `01`, `10`, `11`, `02` or `20` (variants of two-symbol pairs). The sweep rules permute and transfer counts; the expansion rules scale one count linearly in another. Halting condition: a specific block reaches 0 or 1 while the state head meets the halt cell `C 0`.

If true, this is structurally analogous to Bigfoot's `A(a, b, c)` reduction but with more variables. Worth chasing.

## Path forward (Trevor's options)

1. **Deeper rule extraction on 153.** Push to 100k loops, get all 16 rules, write them up systematically. ~1 evening of work.
2. **Derive the underlying parametric system** (the "153 reduction"). Match Shawn's Bigfoot writeup structure. ~few sessions.
3. **State the 153 conjecture as a `Prop`** in Lean (`Bigfoot/Holdout153/Hypothesis.lean`). Trivial once #2 is in hand.
4. **Sketch a TM model + reduction** for 153 in Lean (Phase B for *this specific machine*).
5. *Only then* compare notes with Shawn.

For 397 and 531: different game. They didn't surrender rules to Quick_Sim's defaults. Worth trying `--recursive --block-size N` for various N, and `CPS.py` / `Backtracking_Filter.py`. May be a longer hunt.

## Files

```
sim/Bigfoot.txt              # 5000-loop summary
sim/Holdout_397.txt           # 5000-loop summary
sim/Holdout_153.txt           # 5000-loop summary
sim/Holdout_531.txt           # 5000-loop summary
sim/153_verbose_full.txt      # full --verbose-prover output (750 lines, 11/16 rules)
sim/153_rules.txt             # (empty - grep miss; replaced by verbose_full)
```
