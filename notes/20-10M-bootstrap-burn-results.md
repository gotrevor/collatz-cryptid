# 10M Bootstrap-Burn Results — quantitative confirmation of community consensus

Ran on 2026-05-26 evening through 2026-05-27 ~00:50 EDT. Both BB(3,3) probviously-non-halting holdouts (397 / Fat Coyote, 531 / Wily Coyote) put through a 10M-macro-loop streaming burn with full reversal-config capture (`bb33_397_burn.py --capture-reversals`) and per-head-signature cumulative-novelty analysis (`bb33_bootstrap_novelty.py`).

**Calibration before reading.** The empirical conclusion for 397 — "unbounded auxiliary state, strictly harder than Bigfoot, no clean parametric form" — is *community consensus* on the bbchallenge Discord (LegionMammal, mxdys, others have been on these holdouts for years; see [[reference-bb-community-uses-rocq]]). The 10M data on our specific quantitative axis is new to us; the conclusion is not new to the field. What is new and load-bearing is **(a)** the Lean-side scaffold for FatCoyote (Lean has no Rocq-equivalent of `BB33_494.v` for the unsolved holdouts; we just put a Machine + Hypothesis on the board), and **(b)** the TM-generic reversal-burn + per-head-sig novelty-curve pipeline, which could be reused by community researchers regardless of proof assistant.

The supersession of `notes/15`'s internal case-split (40% on saturation) is real *for our internal posterior* — but it would not surprise anyone on the Discord.

## Run parameters

| Holdout | TM string | --max-loops | --sample-rate | Wall time | Reversals (peaks/valleys) |
|---|---|---|---|---|---|
| 397 | `1RB1LB2LC_1LA2RB1RB_---0LA2LA` | 10M | 1 (all) | 5h 49m | 4462 / 4463 |
| 531 | `1RB2LA1LA_2LA0RA2RC_---0LC2RA` | 10M | 100 | 8 min | 11,694 sampled (1.17M each direction) |

The 60× reversal-rate gap between 397 and 531 (~500 loops/cycle vs ~8.5 loops/cycle) is itself a structural signal — 531 has a *bounded short stack*, 397 has a *growing long stack*. Sampling at rate 100 for 531 brought its file size from a projected 900MB+ down to ~7MB without losing any distributional information.

## 397 (Fat Coyote): valley bootstrap UNBOUNDED — case 1 refuted at 10M

### Peaks (the strong case)

Both dominant peak signatures (~2230 snapshots each) show **100% unique L-bootstrap words** at 10M loops. The novelty curve slope is exactly 1.0 — every cycle produces a previously-unseen bootstrap word, with no decay.

```
<left A, cell=02>  n=2230   L: 2220 distinct (100% unique)   slope=1.00   → UNBOUNDED
<left C, cell=20>  n=2230   L: 2220 distinct (100% unique)   slope=1.00   → UNBOUNDED
```

At the 200k baseline (notes/15), peak uniqueness was 97%. At 10M it is 100%. The pattern **hardened with more data**, not softened. This was already strong evidence for unbounded auxiliary state at peaks; the 10M run confirms it.

### Valleys (the decisive case — this is what notes/15 was uncertain about)

`notes/15`'s 40% prior on "case 1: valley bootstrap saturates" was based on `<right B, 11>` valleys at 200k showing ratio 0.83 (UNBOUNDED?-tentative). The 10M data is unambiguous:

```
<right B, cell=11>  n=2033   L: 472 distinct (23%)   ratio=1.38   slope=0.24   → UNBOUNDED
<right B, cell=21>  n=1970   L: 549 distinct (28%)   ratio=1.18   slope=0.28   → UNBOUNDED
<left B,  cell=12>  n=231    L:  34 distinct (15%)   ratio=1.00   slope=0.20   → UNBOUNDED
<left A,  cell=22>  n=118    L:  36 distinct (31%)   ratio=0.57   slope=0.31   → UNBOUNDED
```

**The valley novelty ratio went UP from 200k to 10M for the dominant signatures**:

| Signature | 200k ratio | 10M ratio |
|---|---|---|
| `<right B, 11>` | 0.83 | **1.38** |
| `<right B, 21>` | 0.60 | **1.18** |

Ratio = (novel words in last decile) / (novel words in first decile). Ratio > 1 means the bootstrap reachable set is growing *faster* in the second half of the run than the first. This is the opposite of saturation — it's mild acceleration, consistent with the linear push-run growth at slope 0.5/cycle scaling the available structural room.

Two minor signatures (`<right B, 12>`, `<right B, 22>`) show ratio 0.00 and 0.50 respectively, but their sample counts are tiny (n=54, n=49) — they are transient or rare states. They cannot rescue case 1.

### Updated case split for 397

`notes/15` posterior (before this experiment):

| Case | Prior |
|---|---|
| Bigfoot-shaped clean (a, b, c) | 15% |
| Bounded counter automaton (case 1) | 40% |
| Strictly harder than Bigfoot (case 2) | 35% |
| Other / hybrid | 10% |
| Unknown | 5% |

`notes/20` posterior (after 10M data):

| Case | Posterior |
|---|---|
| Bigfoot-shaped clean (a, b, c) | <1% — peaks 100% unique kills it |
| Bounded counter automaton (case 1) | <1% — valley ratios 1.18-1.38 kill it |
| **Strictly harder than Bigfoot (case 2)** | **~97%** |
| Other / hybrid (case 4) | ~2% |
| Unknown | <1% |

**Fat Coyote / 397 has unbounded auxiliary state.** Any finite parametric form would have produced a saturating reachable-set curve at *some* head signature. None of the dominant signatures do.

The Lean implication: a `Dynamics.lean` for FatCoyote should not commit to a concrete finite `Σ_valley` type. The right shape is the abstract `SweepPDA` framework with `opaque` reachable-bootstrap (the second alternative in `notes/19`'s sketch).

## 531 (Wily Coyote): radically different structure

531 has a single dominant peak signature and a single dominant valley signature (vs 397's six). Both show **saturated left bootstrap** (1 distinct word across 11,694 sampled snapshots) and **slow but ongoing growth on the right bootstrap**:

```
PEAKS    <left A, cell=12>   L: 1 distinct (saturated)   R: 4531 distinct (39%)   ratio=0.40   slope=0.32   → slowing
VALLEYS  <right A, cell=10>  L: 1 distinct (saturated)   R: 4102 distinct (35%)   ratio=0.39   slope=0.28   → slowing
```

531's bootstrap is *partially* saturating. The "slowing" verdict means novel-words-in-last-decile / novel-words-in-first-decile is between 0.1 and 0.5 — not full saturation, but the reachable set is growing measurably slower per cycle than at the start.

If 531's R-bootstrap continues to slow at the observed rate, it might saturate at some O(10⁴–10⁵) distinct words. Or it might log-grow indefinitely. The 10M data doesn't discriminate.

### Updated reading on 531 (vs notes/13 / notes/12)

`notes/13` refuted the *bounded-length-on-left* hypothesis (max word length grew 24→33 from 200k → 10M loops). The 10M-bootstrap data is consistent with that finding and adds structure: **the LEFT side reachable-bootstrap is saturated at 1 word, the LEFT side reachable-length is growing.** Both are simultaneously true because the "1 word" is a constant *bootstrap*; the LEFT growth is in the *periodic body length* `N_left`.

So 531 looks like:
- Left: pure periodic stack with one-word bootstrap, growing length.
- Right: irregular auxiliary state with slow-growth reachable set.

This is a much *cleaner* structure than 397's both-sides-growing pattern. **531 may admit a finite-state-counter reduction** (counter = N_left; auxiliary state = current R-bootstrap word from a slowly-growing reachable set). Resolving this requires more sweep cycles or finer sampling.

## What lands in Lean

The 10M result changes the right Lean shape for FatCoyote and clarifies it for Wily Coyote.

### FatCoyote (397)

`notes/19`'s sketch had two alternatives:

```lean
-- Alternative A (saturation): committed to concrete finite Σ_valley type. NOW DEAD.

-- Alternative B (unbounded): abstract SweepPDA framework with opaque reachable type.
structure SweepPDA where ...
```

Alternative A is dead. Alternative B is the right shape. **`Collatz/BB/SweepPDA.lean` would be the first Lean-side encoding of a sweep-PDA-with-unbounded-auxiliary BB analysis framework** — small framework contribution regardless of whether anyone proves 397's non-halt.

### WilyCoyote (531)

The cleaner structure makes 531 a *better* target for a Phase-1 finite-state-counter `Dynamics.lean`. Sketch:

```lean
structure WilyCoyoteCfg where
  leftBody    : ℕ              -- the saturated-bootstrap repeat count
  rightBoot   : RightBootWord  -- inductive over (currently) ~4500 observed states
  cyclePhase  : SweepPhase
```

Whether `RightBootWord` is a finite inductive (case 1 still viable for 531) or an opaque type (case 3) is the open question. Worth a 100M-loop burn with finer sampling to discriminate.

## Calibration retrospective

`notes/15`'s 40% prior on case 1 (saturation) for 397 was wrong-side-of-50%. The 10M data drops it to <1%. Worth examining *why* the small-sample valley data at 200k looked saturation-ish: 281 snapshots, ratio 0.83. The "novelty curve flattens with more data" hypothesis was the natural read of those numbers in isolation. The right test was simply more data, which we now have.

Same lesson as `notes/13` (531 saturation refuted) and `feedback_research_claims_rigor.md`: push 1-2 orders of magnitude past the originating sample size before naming a finding structural. 200k → 10M is the right calibration burn.

## Files

- `sim/397_burn_10M_v2.json` — final 397 burn checkpoint summary (5h 49m runtime)
- `sim/397_burn_10M_v2.reversals.json` — 4462 peaks + 4463 valleys, full configs
- `sim/531_burn_10M.json` — final 531 burn checkpoint summary (8 min runtime)
- `sim/531_burn_10M.reversals.json` — 11,694 sampled peaks + valleys (rate 1/100, 1.17M total each direction)
- `/tmp/burn_summary.csv` — per-(file, kind, head_sig) saturation metrics
- `/tmp/burn_curves.csv` — full per-snapshot novelty curves for plotting
- `tools/sandbox/bb33_397_burn.py` — extended with `--capture-reversals`, `--reversal-sample-rate`, `--tm` flags, uv-run shebang
- `tools/sandbox/bb33_bootstrap_novelty.py` — new structured-output novelty analyzer

## Next moves

1. **Update `Collatz/FatCoyote/Hypothesis.lean` docstring** — note that 10M empirical analysis confirms unbounded auxiliary state; the TM-level hypothesis remains the only honest formal Prop until a SweepPDA framework lands.
2. **Sketch `Collatz/BB/SweepPDA.lean`** — abstract framework with opaque reachable-bootstrap type, plus `instance : SweepPDA FatCoyote.machine`. Small but *first*.
3. **Decide on 531 next step** — either a 100M burn with sample rate 10 to test R-bootstrap saturation, or an `analysis_531.py` that probes whether the R-bootstrap words form a recognizable language (substitutive? regular? PDA-recognizable?).
4. **Community surfacing question** — does the bbchallenge Discord want this kind of quantitative 10M-burn data on Fat Coyote? Per [[reference-bb-community-uses-rocq]], they're in Rocq; the Lean side is ours. The empirical result (data + script) is language-agnostic and shareable independently.
