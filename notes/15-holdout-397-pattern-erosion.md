# Holdout 397 - Pattern Erosion Under Deeper Inspection 📉

**Supersedes claims in `14-holdout-397-pushdown-sweep.md`** about a clean Bigfoot-style 3-counter reduction. The sweep PDA structure survives; the parametric (a,b,c) reduction does not.

## TL;DR

What `notes/14` claimed:
- Pure pushdown sweep with linear +0.5/cycle growth ✅ **survives**
- 7-state head controller with clean head→(P_left, P_right) lookup → **partially** survives
- Bigfoot-shaped 3-integer-counter reduction → **does NOT survive**

What we now see, after extracting 623 PEAK + 623 VALLEY full configurations from the cached 200k trace and decomposing each:

| Claim from notes/14 | Status at 623-snapshot scale |
|---|---|
| Sweep PDA (100% boundary edits) | ✅ confirmed |
| Linear run-length growth, +0.5/cycle | ✅ confirmed (R² climbed to 0.9999 at 2.5M loops, see burn data below) |
| ~7 dominant head states, finite-state control | ✅ confirmed (12 states observed, 7 dominant 98%+) |
| Clean head→(P_left, P_right) lookup table | ⚠️ partial — patterns are stable *modulo phase shift* but each head signature has 2 phase variants and rare exotic variants |
| (a, b, c) = 3 integers + head state is the full reduction | ❌ **refuted** — bootstrap word is auxiliary state, evolving cycle to cycle |
| 397 admits a Bigfoot-style parametric reduction | ⚠️ unknown; needs longer data to resolve |

The cost of being wrong: an over-confident jump from `notes/12` ("substitutive ~50%") through `notes/14` ("Bigfoot-shaped ~85%") to here ("uncertain, plausibly harder than Bigfoot, possibly bounded-finite-state, possibly unbounded"). Trevor flagged this would happen: "patterns likely evaporate upon deeper exploration."

## The 2.5M-loop calibration burn

Before the parametric question, the linear-growth claim got a 12.5× calibration burn (200k → 2.5M cached + streamed):

```
              200k cache     500k pilot    2.5M streamed burn
push slope:   0.500          0.498         0.4992
push R²:      0.9985         0.9956        0.998
pop slope:    0.498          0.500         0.5000
pop R²:       0.9928         0.9993        0.9999       ← five 9s
cycles:       624            991           2227
push max:     318            502           1119
head states:  12             12            12          ← locked
```

R² *increases* with more data. Slope holds at exactly 0.5 per sweep cycle. The head signature set does not expand. The macro-structure is real.

The burn was killed at 2.5M loops because wall-time-per-loop grew faster than linear (each macro-loop's chain-steps cover more cells), and the calibration question was already answered.

## Reversal-snapshot decomposition

Across all 623 push→pop reversal points (PEAKS) and 623 pop→push reversal points (VALLEYS) in the 200k cached trace, we auto-decompose each tape configuration:

```
00^inf · [LEFT_BOOTSTRAP] · (P_left)^N_left · HEAD · (P_right)^N_right · [RIGHT_BOOTSTRAP] · 00^inf
```

Pattern detection chooses the longest contiguous period-≤4 window of identical tokens on each side; whatever doesn't fit becomes "bootstrap" on the far side from the head.

**Asymmetry between peaks and valleys**:

| | At peaks (push→pop) | At valleys (pop→push) |
|---|---|---|
| Head position | Left end of sweep (deep on the left stack) | Right end of sweep (next to growing right block) |
| Long body | LEFT side (`P_left`)^N_left | RIGHT side (`P_right`)^N_right |
| Bootstrap | LEFT-most ~15-20 tokens | LEFT-most ~0-12 tokens (most of LEFT is consumed) |
| `N_left` range | [1, 155] (growing with cycle) | [0, 4] |
| `N_right` range | [0, 0] (right side is just a tail token) | [0, 156] (growing with cycle) |

So at peaks the LEFT counter `a := N_left` lives; at valleys the RIGHT counter `b := N_right` lives. They swap each half-cycle as the head bounces.

## Pattern stability per head signature

**At peaks**, `P_left` is essentially ONE period-2 pattern per head signature, modulo phase shift:

| Head signature | Snapshots | P_left distribution |
|---|---|---|
| `<left A, 02>` | 310 | `(12,22)`:229, `(22,12)`:77, exotic:4 |
| `<left C, 20>` | 311 | `(21,22)`:153, `(22,21)`:152, exotic:6 |

`(12,22)` and `(22,12)` are the same alternating word read from offset 0 vs offset 1. The two head signatures see two distinct fundamental period-2 patterns: `121212...22` for A-state heads, `212121...22` for C-state heads. Clean.

**At valleys**, `P_right` is similarly stable (small phase variants of one period-2 pattern). The patterns observed in `notes/14`'s 4-sample inspection (`(22,20)`, `(20,22)`, `(02,22)`, `(22,02)`) all confirm.

## What broke: the bootstrap

The killer finding. Bootstrap reachable set:

**At PEAKS** — bootstrap is the leftmost ~15-20 tokens, on the far side of the head from the growing body:

```
<left A, 02> peaks: 310 snapshots → 301 distinct bootstrap words (97% unique)
<left C, 20> peaks: 311 snapshots → 301 distinct bootstrap words (97% unique)
```

Novelty curve at peaks is **essentially linear** — almost every cycle produces a new bootstrap word that's never been seen before. After 310 snapshots, 301 distinct words, still adding ~31 new per 31 snapshots.

**At VALLEYS** — bootstrap is much shorter (0-12 tokens), reachable set is smaller but still growing:

```
<right B, 11> valleys: 281 snapshots → 66 distinct bootstrap words (23% unique)
<right B, 21> valleys: 268 snapshots → 76 distinct bootstrap words (28% unique)
```

Novelty curve for `<right B, 11>` valleys: 7, 14, 23, 25, 35, 41, 47, 55, 61, 66 distinct (after each successive batch of 28 snapshots). Differences: 7, 9, 2, 10, 6, 6, 8, 6, 5. Slight downward trend (could be early saturation, could be slow-but-unbounded growth).

**The asymmetry**: at peaks, information is being CREATED (each cycle adds new history to the far-left); at valleys, the left side is mostly consumed and history is partially erased. The valley reachable set might saturate at finite size — or it might keep growing slowly. The 200k-loop trace doesn't resolve this.

## Implications for the parametric reduction

`notes/14`'s claim was: 397 reduces to a (a, b, c)-parameterized Bigfoot-like recurrence on 3 integer counters + a 7-state head controller. This is **false** because the bootstrap word at peaks accumulates cycle-by-cycle history. The "auxiliary state" is at least a finite word over a 5-symbol alphabet of length up to ~20, but the *reachable set* across cycles is what matters.

Three scenarios:

1. **Valley bootstrap set saturates** (e.g., at ~hundreds of distinct words). Then 397 has a clean finite-state-counter reduction (counter automaton-style), albeit with much more state than Bigfoot's 3 integers. The peak bootstraps are just a "view" of the larger context that includes additional accumulated structure, but the cycle-to-cycle transition is governed by the valley state alone. **Estimated probability: ~40%.**

2. **Valley bootstrap set grows without bound** (sub-linear, but unbounded). Then 397 has unbounded auxiliary state and is *strictly harder* than Bigfoot — there's no finite parametric form to even *state* the non-halting hypothesis. **Estimated probability: ~35%.**

3. **Bigfoot-shaped clean 3-integer reduction exists** but my decomposition failed to find it (e.g., the "bootstrap" is actually fitting a different parametric form I haven't tried). **Estimated probability: ~15%.**

Other / hybrid: ~10%.

## What would discriminate

The decisive experiment: run Quick_Sim out to 10M+ macro-loops with full reversal-snapshot capture, then compute the novelty curve for valley bootstrap words across all sweep cycles at each head signature. If the curve flattens to a horizontal asymptote, case 1 (decidable). If it keeps growing logarithmically, case 2 (harder than Bigfoot).

Cost: ~3-5 hours of CPU per the 2.5M extrapolation. Not done in this session.

## Confidence calibration retrospective

`notes/12` → `notes/14` → `notes/15` trajectory:

| Note | Date | Hardness claim | Confidence |
|---|---|---|---|
| 12 | 2026-05-23 | substitutive sequence (notes/12 hypothesis) | ~50% |
| 14 | 2026-05-25 (early) | Bigfoot-shaped (case 2) | ~85% |
| 15 | 2026-05-25 (later) | uncertain, leaning case 2.5/3 | (15/40/35/15/5 split across cases) |

Trevor's standing guidance from `feedback_research_claims_rigor.md` (the 531-saturation burn) applied:

> Push 1-2 orders of magnitude beyond initial observation before naming a finding structural.

The `notes/14` claim was made on:
- 624-cycle linear regression (sound)
- **4-snapshot inspection of full configs** (unsound)
- Eyeball pattern matching that didn't survive when scaled to 623 snapshots.

The right move would have been to inspect ≥100 snapshots before claiming the lookup table was clean. The pattern at 4 samples was a phase-coincidence; at 623 samples the underlying complexity surfaced.

## Files

- `tools/sandbox/bb33_397_burn.py` — streaming long-trace harness (used for 2.5M calibration)
- `tools/sandbox/bb33_397_extract_reversals.py` — extracts peak/valley full configs from cached trace
- `tools/sandbox/bb33_397_bootstrap_analysis.py` — decomposes each reversal config, bootstrap novelty curves
- `sim/397_reversals.json` — 623 peaks + 623 valleys, full token strings
- `sim/397_burn_500k.json`, `397_burn_10M.json` — checkpoint stats from streaming burns (500k complete, 10M killed at 2.5M)

## What's still solid (the floor)

- 397 is a sweep PDA. Confidence ~100%.
- Sweep run-length grows linearly at slope 0.5 per cycle, with R² ≥ 0.998 across all measured scales up to 2.5M loops / 2227 cycles. Confidence ~99%.
- Head signature set is finite (12 observed states, 7 dominant). Confidence ~95%.
- 397 is empirically non-halting up through 2.5M macro-loops (~7.5M TM-steps). Confidence ~99% (well-established prior).

What's NOT solid: the clean Bigfoot reduction. That was an over-claim from small-sample inspection.

## Connecting back to the question Trevor asked

> "Is it still hard? You compare it to Bigfoot, so it's still hard?"

Best honest answer now: **probably at least as hard as Bigfoot, possibly harder.** The 75% of the case-2.5/case-3 probability mass is the "structure exists but its full description needs more state than 3 integers" zone. Bigfoot's clean parametric form is what gives it its "decidable conditional on Bigfoot.Hypothesis" structure; 397 may lack that property and instead require an unbounded-state argument.

The cleanest path forward (if continuing): the 10M reversal-burn to settle case 1 vs case 2/3, then either declare a counter-automaton model or accept the harder-than-Bigfoot conclusion.
