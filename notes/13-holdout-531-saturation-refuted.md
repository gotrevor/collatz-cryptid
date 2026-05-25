# Holdout 531 - Reachable-Word Saturation REFUTED ❌

Follow-up to `12-holdouts-397-531-factor-complexity.md`. Yesterday's headline for 531 was *bounded word length (max 24) + bounded factor complexity*, with a hypothesis that the right-side word lives in a finite reachable set, which would make 531 a counter-automaton candidate and potentially decidable.

**The 10M-loop saturation test refutes that hypothesis on both axes.**

## Method

`tools/sandbox/bb33_531_saturation.py` - streams Quick_Sim verbose output for 10M macro-loops, hashes each right-side word, tracks total distinct words and current/max word length. CSV at `sim/531_saturation.csv`.

Wall time: 470 seconds (~22k macro-loops/sec). Memory: ~600 MB for the 3M-element word set.

## Headline

| step | distinct words | current wlen | max wlen so far | new in last 100k |
|---|---|---|---|---|
| 200k | 61k | 17 | 17 | (baseline) |
| 1M | 308k | 22 | 22 | ~30k |
| 5M | 1.5M | 25 | 30 | ~30k |
| **10M** | **2.96M** | 23 | **33** | ~30k |

- **Distinct word count grows LINEARLY with step count.** ~30k new distinct words per 100k macro-loops, throughout the trace. No saturation hint anywhere.
- **Max word length is NOT actually bounded.** Yesterday's "max 24" at 200k loops was a sampling artifact. Length keeps growing: 24 → 30 by 5M loops, 33 by 10M loops. The growth is roughly logarithmic / very-slow-power-law, but unbounded.

## Interpretation

The "bounded right-side word → finite-state-counter automaton" model is wrong. 531 doesn't have a finite reachable set of right-side states. It might still have *some* structure, but not the simplest kind we hypothesized.

What 531 actually looks like:
- **Word length grows slowly** with step count (log/power-law). 24→33 over 50× more loops.
- **Word variety grows linearly** with step count. ~30% new words per snapshot, throughout 10M loops.
- **Factor complexity per snapshot remains bounded** (yesterday's c(n) ≤ 22 finding still holds locally - each individual snapshot has bounded factor complexity).

So each snapshot is a *low-complexity word*, but the SEQUENCE of snapshots draws from an ever-growing pool. The dynamics is producing a parameter family of words, parameterized by something that keeps incrementing.

## Updated taxonomy

| | Bigfoot | 153 | 397 | 531 |
|---|---|---|---|---|
| Macro shape recurrence | high | high | none | almost none |
| Word factor complexity | (not measured) | (not measured) | bounded ≤ 22 | bounded ≤ 22 (per snapshot) |
| Word length | exp growth | poly growth | linear growth | **log/slow growth** (unbounded) |
| Reachable word set | (presumably finite via a,b,c) | (16-rule structure) | (growing word family) | **infinite** |
| Quick_Sim rules | 2 | 16 | 0 | 0 |
| Candidate framework | counter triple | shape-explosive | substitutive | ~~counter automaton~~ - REFUTED |

## What's left for 531

The "infinite reachable word set" finding doesn't kill all decidability hopes - it just kills the *simplest* one. 531 could still be:

- **Counter automaton with growing word**: maybe the right-side word is a *function* of multiple counters, and as the counters grow the word gets longer. If the function is computable, 531 might still be decidable via counter-machine techniques.
- **Two-counter / multi-counter automaton**: known to be Turing-complete in general, but specific instances may be decidable.
- **Substitutive structure**: maybe consecutive snapshots are related by a finite substitution that elongates the word. Worth testing.

But these are deeper / less likely / more open-ended. Without an inroad, **531 doesn't look like the most tractable BB(3,3) holdout after all**. Bigfoot remains the best target for the formalization effort.

## Cost of being wrong

Yesterday I wrote that 531 was "potentially the most tractable open BB(3,3) holdout" with ~60% confidence. That's now refuted. Calibrated 60% means 40% chance of being wrong, and this is where the 40% landed. Note for future me: when a bounded-X finding comes from a 200k-sample window, push the sample size up at least 1-2 orders of magnitude before naming it a structural claim.

## Files

- `tools/sandbox/bb33_531_saturation.py` - the streaming tool
- `sim/531_saturation.csv` - 100 sample points (step, distinct, wlen, ...)
