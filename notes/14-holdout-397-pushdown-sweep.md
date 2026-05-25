# Holdout 397 - Pushdown Sweep Structure 🌊

> ⚠️ **Partially superseded by `15-holdout-397-pattern-erosion.md` (2026-05-25 same day).** The sweep PDA structure and linear run-length growth claims below SURVIVE deeper inspection (623 reversal snapshots + 2.5M-loop streaming burn). The "extension to Bigfoot-shaped (a,b,c) parametric reduction" claim in the *open questions* section DOES NOT survive — the bootstrap word at peak reversals is ~97% unique per cycle, so 397 has at least *some* unbounded auxiliary state beyond a clean 3-counter form. Read `notes/15` for the calibrated picture.

Follow-up to `12-holdouts-397-531-factor-complexity.md`. That note's substitution hypothesis (~50% confidence) for 397's left-side macro word predicted exponential growth under a fixed substitution σ. **The substitution hypothesis is refuted; what we find instead is a much cleaner structure: 397's left-side word evolves as a pure pushdown automaton with a sweep controller.**

## TL;DR

- **No substitution σ fits.** k=1 uniform fails immediately (t=24); k=2 fails at t=112; variable-length k=1 length-prediction is not exact.
- **Δ|W| ∈ {-1, 0, +1} for 100% of macro-steps.** Distribution: +1 (47.6%), -1 (47.2%), 0 (5.2%) over 10k pairs.
- **All edits are at the RIGHT boundary of the left-side stack.** 100% of pushes at position 0 from the right, 100% of pops at position 0 from the right, replaces (~0.6%) also at the right boundary.
- **Pushes and pops come in strictly alternating runs.** Across 200k snapshots, 1247 maximal runs, **100.0% strict alternation** between push runs and pop runs.
- **Run-length statistics**: push runs mean 158.40 (max 318), pop runs mean 158.12 (max 320). Range [1, 320].
- **Net growth**: median (push_run - pop_run) = +1 per cycle, mean +0.41 per cycle. Cumulative +507 symbols over 1247 cycles. This matches notes/10's observation of "linear word-length growth."

## Methodology

Driver scripts (added today):
- `tools/sandbox/bb33_397_substitution.py` - substitution-hunt (Δ|W|, uniform σ, variable-length σ, k-step σ, boundary alignment).
- `tools/sandbox/bb33_397_stack_behavior.py` - classifies each macro-step as push / pop / replace / same / complex; reports edit position from both ends.
- `tools/sandbox/bb33_397_pda.py` - tests whether action is a deterministic function of the top-k stack symbols (for k=1..6).
- `tools/sandbox/bb33_397_sweeps.py` - run-length statistics on push/pop runs.

All reuse `parse_configs` / `token_to_symbol` from `bb33_complexity.py`. Trace input: `sim/complexity_397_b2_l200000.txt` (200k macro-loops, block size 2, every config printed).

## Findings in detail

### Pushdown structure (100% boundary edits)

Per `bb33_397_stack_behavior.py` over 20k pairs (5-symbol alphabet `{01, 11, 12, 21, 22}`):

| edit kind | count | % |
|---|---|---|
| push | 9661 | 48.3% |
| pop | 9584 | 47.9% |
| same | 638 | 3.2% |
| replace | 116 | 0.6% |

Position of push edits (from RIGHT end of `W[t+1]`): **9661/9661 = 100.0% at position 0**. Same for pops in `W[t]`. The few "replace" edits (0.6%) also occur at the rightmost position.

The "complex" bucket (multi-symbol edit or non-boundary edit) is empty over 20k pairs. **397 is a pure pushdown on the left-side word: at each macro-loop, exactly one of {push X, pop, replace top, no-op} happens at the top of the stack.**

### Symbol distribution on push/pop

| symbol | push count | pop count |
|---|---|---|
| `22` | 4699 | 4703 |
| `21` | 2360 | 2318 |
| `12` | 2356 | 2394 |
| `11` | 243 | 166 |
| `01` | 3 | 3 |

The push and pop symbol distributions are nearly identical for `22`/`21`/`12`/`01` (within 1% relative), and modestly skewed for `11` (243 pushed vs. 166 popped over 20k). This near-equality is expected: in a sweep, the symbol pushed during the rightward phase is the same one popped on the next leftward phase.

### Action NOT determined by top-k (k ≤ 6)

Per `bb33_397_pda.py` over 50k pairs:

| k | distinct top-k contexts | deterministic contexts | minority-action rate |
|---|---|---|---|
| 1 | 5 | 0/5 | 51.31% |
| 2 | 13 | 0/13 | 51.16% |
| 3 | 37 | 0/37 | 50.95% |
| 4 | 99 | 0/99 | 50.77% |
| 5 | 210 | 0/210 | 50.67% |
| 6 | 371 | 2/371 | 50.52% |

Every nondeterministic context has the same character: a **push action and a pop action of nearly equal frequency**, with a small tail of `same`/`replace`/minor pushes. Example (k=2, context `[22 12]`):

```
('pop', '12'): 5851
('push', '22'): 5837    ← virtually identical count
('push', '11'): 26
('same',): 26
('replace', ('12', '11')): 15
('push', '21'): 12
```

The clean 50/50 split is the signature of **hidden state with two values** - the sweep direction - which the top-k of the stack does not encode. (The TM's underlying head-position-and-state encodes it; the visible stack alone does not.)

### Sweep dynamics: 100% alternation

Per `bb33_397_sweeps.py` over 200k pairs:

- 1248 maximal push/pop runs (624 push runs, 624 pop runs).
- **1247/1247 = 100.0% strict alternation** between push runs and pop runs.
- Push run lengths: mean 158.40, median 159, p99 312, max 318.
- Pop run lengths: mean 158.12, median 158, p99 310, max 320.

Sample of the first 30 runs:

```
push 1  pop 1   push 3  pop 3   push 4  pop 2   push 2  pop 1
push 1  pop 4   push 8  pop 8   push 7  pop 2   push 4  pop 3
push 3  pop 7   push 8  pop 10  push 11 pop 5   push 6  pop 5
push 5  pop 8   push 9  pop 11  push 11 pop 6
```

Run lengths drift slowly and unpredictably; consecutive pairs `(push_run, pop_run)` differ by anywhere from -12 to +164 with median +1 and mean +0.41. The mean of +0.41 per cycle is the linear growth rate of `|W|` over time (consistent with the "mean length 115.5 over 200k snapshots" measurement in notes/12).

## Updated taxonomy

Combining with prior work:

| | Bigfoot | 153 | 397 | 531 |
|---|---|---|---|---|
| Macro shape recurrence | high (28.7% distinct) | high (31.5%) | none (100%) | almost none (95.8%) |
| Word factor complexity | ? | ? | bounded ≤ 22 | bounded ≤ 21 |
| Word length | exp growth | poly growth | linear growth | bounded (≤ 24) |
| Δ|W| per macro-step | varies (block rules) | varies | **±1 (94.8%) + 0 (5.2%)** | ? (not measured) |
| Edit locality | sweep over counters | sweep | **100% right boundary (PDA)** | ? |
| Run structure | ? | ? | **strict push/pop alternation** | ? |
| Quick_Sim rules | 2 | 16 | 0 | 0 |
| Candidate framework | counter triple `(a,b,c)` | shape-explosive | **sweep PDA + run-length controller** | counter automaton |

## Why Quick_Sim found 0 rules

Quick_Sim's block-finder looks for *repeated configurations within a single macro-loop* and proposes rules of the form "macro-config X transforms into macro-config Y" for matching shapes. **397's macro-configs almost never recur** (notes/10: 100% distinct shape signatures). The sweep structure exists across *consecutive* macro-loops but never produces a recognizable closed-form block-rule, because each loop only edits one symbol. Quick_Sim does not search for one-symbol-per-loop structure - that pattern is too fine-grained for its rule template.

This explains the apparent paradox in notes/10: "more shape-explosive than 153, no rule structure" turns out to mean "structure exists, but at a lower level than Quick_Sim's rule templates can express."

## What this opens up (open questions)

1. **Is the run-length sequence computable?** We have 624 push-run lengths and 624 pop-run lengths. Treat them as two integer sequences indexed by sweep cycle. Is there a closed-form recurrence? Is the OEIS aware of these sequences? Are they ~near-periodic, near-random, or governed by a simple counter automaton?

2. **What's the run-length controller's hidden state?** The simplest model would be a 2-counter automaton on `(stack_height, sweep_phase)`; the actual TM is presumably more constrained. Extracting that controller would be tantamount to a Bigfoot-style parametric reduction for 397.

3. **Does the right-side block grow predictably across sweeps?** We focused on the left-side stack. The growing right block (`2022^N`) is presumably driven by the same sweep cycles - each round trip likely increments `N` by a fixed (or slowly-varying) amount.

4. **Decidability via sweep model.** If the run-length controller is finite-state-plus-counter, then 397's non-halting could in principle be proved by a structural argument akin to Bigfoot's. Concretely: characterize the (initial-condition → eventual halt) reachability question for the run-length controller.

5. **Does 531 have the same sweep structure?** notes/12 reports 531 has *bounded* word length (max 24) - so it can't be a simple sweep PDA (those produce unbounded length). 531 might be a finite-state-counter system on a different axis. Worth running these same scripts on 531.

## Reproducibility

```bash
sandbox ~/src/collatz-cryptid/tools/sandbox/bb33_397_substitution.py --limit 10000
sandbox ~/src/collatz-cryptid/tools/sandbox/bb33_397_stack_behavior.py --limit 20000
sandbox ~/src/collatz-cryptid/tools/sandbox/bb33_397_pda.py --limit 50000 --k-max 6
sandbox ~/src/collatz-cryptid/tools/sandbox/bb33_397_sweeps.py --limit 200000
```

All four read the cached trace at `sim/complexity_397_b2_l200000.txt`. No new Quick_Sim runs.

## Files

- `tools/sandbox/bb33_397_substitution.py`
- `tools/sandbox/bb33_397_stack_behavior.py`
- `tools/sandbox/bb33_397_pda.py`
- `tools/sandbox/bb33_397_sweeps.py`
