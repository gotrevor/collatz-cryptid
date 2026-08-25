# Bootstrap-Language Structural Probe — 397 vs 531

Ran 2026-05-27 ~02:00 EDT on the same 10M reversal data from `notes/20`. New script: `tools/sandbox/bb33_bootstrap_structure.py`. The probe asks WHAT KIND of language the distinct bootstrap words form, not just how many there are.

## Refinement of `notes/20`'s framing

`notes/20` claimed 397 has "unbounded auxiliary state." The probe shows that was *partly* wrong:

* The bootstrap WORDS are bounded length (max 26 for 397, max 23 for 531).
* What's unbounded for 397 is the *reachable SET of bounded-length words*.
* For 531, both individual words AND the reachable set are bounded (though the set is large, slowly growing).

So the corrected framing: **both holdouts' bootstrap words live in a bounded-depth trie over a 5-symbol alphabet; 531's trie is densely populated and slow-growing, 397's trie is sparsely populated and explores new branches every cycle.**

In principle the max-length-26 bound means 397's reachable bootstrap set is finite (≤ 5^26 ≈ 1.5×10¹⁸). In practice at the observed 1-new-word-per-cycle rate, we'd need ~10²⁵ cycles to exhaust it — astronomically out of reach.

## Side-by-side comparison

| | 397 L-bootstrap, peaks | 531 R-bootstrap, peaks |
|---|---|---|
| Distinct words at 10M | 2220 | 4531 |
| Total occurrences | 2230 | 11,694 |
| Unique percentage | 99.6% | 38.7% |
| Word length: min/mean/max | 0 / 16-19 / 26 | 0 / 13 / 23 |
| Alphabet (in frequency order) | {22, 12, 11, 21, 01} | {12, 21, 22, 11, 20, 10} |
| Pos 0 alphabet | {12, 01} — strong bias to 12 | {11, 21, 22, 12} — uniform 4 |
| Pos 1 alphabet | {22, 21} — strong bias to 22 | uniform 4 |
| Pos 2 alphabet | mostly {21}, tiny rest | uniform 4 |
| Prefix-determinism at k=5 | 7% deterministic | 0% deterministic |
| Pure-periodic words | 0% | 0% |
| Extension test: prefix | 100% (every word extends a shorter one) | 100% (same) |
| Extension test: suffix | ~48% | ~99.9% |
| Top-word frequency | every word ≤2× (flat) | top word 1252× (heavy-tailed) |

## What the data says about each holdout

### 531: heavy-tailed, uniform-branching, suffix-anchored

531's R-bootstrap has the structural signature of a **state-recurrent dynamical system**. The top words form a clean pattern:

```
  (20)            1252×    length 1
  (12 20)          340×    length 2
  (21 12 20)       490×    length 3
  (12 21 12 20)    486×    length 4
  (21 12 21 12 20) 376×    length 5
```

Every top word ends in `20` (suffix anchor) and is built by prepending an alternating `12 21 12 21 …` pattern. Suffix-extension is essentially 100% — most words sit on a common suffix backbone.

Uniform per-position branching (all 4 main symbols ~equally likely at every position) means the language is NOT prefix-deterministic — you can't predict the next symbol from a length-5 prefix. But the heavy-tailed frequency distribution + suffix-anchored structure says: the system *visits* a small set of "core" states (the top words) frequently and *occasionally* explores branches.

**Implication**: 531 may admit a finite-state reduction if the R-bootstrap reachable set saturates. The 10M data shows it slowing (notes/20 ratio 0.40) but not yet stopped. A 100M-loop burn at sample rate 10 could resolve this.

### 397: flat distribution, position-biased alphabet, prefix-anchored

397's L-bootstrap is the *opposite*: nearly every word is unique (99.6%), no top frequency, but the alphabet is *strongly position-biased*:

```
  pos 0: {12: 1433, 01: 786}        ← only 2 symbols
  pos 1: {22: 1491, 21: 728}        ← only 2 symbols
  pos 2: {21: 1390, 12: 450, 11: 376, 22: 2}   ← '22' essentially forbidden
  pos 3: {12: 1031, 11: 579, 22: 387, 21: 218}
  ...
```

So 397 has *less branching at the start* and *more uniform branching deeper in*. Roughly: the leading symbol is one of 2 things, the next is one of 2 things, then 3-4-way branching starts.

Combined with 100% prefix-extension and only ~48% suffix-extension: each word is built by **extending a shorter word at its end** with a typically-novel suffix. The system never revisits the same path.

**Implication**: 397's bootstrap-language is consistent with a system that builds up an information-theoretically rich state at each cycle. The position-bias at the start suggests there's a small set of "entry-point" structures, but the system branches outward into mostly-new territory each cycle.

## What this changes / doesn't change

### Doesn't change

- 397's bootstrap reachable set is still effectively unbounded for any feasible analysis horizon.
- `notes/20`'s case-2 verdict (strictly harder than Bigfoot) for 397 stands.
- The Lean-side `Collatz/FatCoyote/SweepPDA.lean` trivial realization is still the right shape.

### Refines

- 397's individual auxiliary state is *bounded in description length* (max 26 tokens). This is a meaningful refinement of "unbounded aux state" — the state has bounded entropy per cycle, but the *trajectory* through state-space is essentially injective for at least 10M cycles.
- 531 looks like a much-more-likely candidate for an actual finite-state reduction than 397. The R-bootstrap heavy-tailed + suffix-anchored structure smells like an automaton with a finite state set being explored slowly.

## Addendum (2026-05-27 morning) — 397 peaks vs valleys asymmetry

Probed 397 valleys L-bootstrap for symmetry with the peaks data above. Result: **valleys are structurally distinct from peaks**, and the contrast sharpens the case-2 reading.

| Head sig (valley) | distinct | max len | top freq | k=5 det |
|---|---|---|---|---|
| `<left A, 22>` | 36 | 8 | 30× (∅) | 95% |
| `<left B, 12>` | 34 | 9 | 67× (∅) | 82% |
| `<right B, 11>` | 472 | 17 | 309× (∅) | 34% |
| `<right B, 21>` | 549 | 18 | 331× (∅) | 25% |

Compare to 397 peaks: 2220 distinct, max len 26, top freq ≤2× (flat), k=5 det 7%.

The most striking finding: **the top-frequent valley bootstraps are the *same short words* across all head signatures**:

```
∅ (empty)        30× / 67× / 309× / 331×
(12)             13× / 30× / 147× / 138×
(01 22)          12× / 26× / 108× / 111×
(01)              7× / 18× /  75× /  80×
(12 22)           8× / 13× /  70× /  62×
```

A small **common core of ~5 short bootstrap states** accounts for the top-frequency mass at every valley signature. The valley reachable set is also much smaller (36, 34, 472, 549 vs 2220, 2220 at peaks) and the words are much shorter (max 8-18 vs max 26).

### What this means structurally

At PEAKS, the bootstrap accumulates full left-side history → information-rich, unique, length-growing.

At VALLEYS, most of that history has been *consumed by the pop run* → only a short residual remains, drawn from a small recurring set.

So 397's dynamics looks like:
1. Pop runs destroy most of the bootstrap, leaving the head in one of a few recurring valley states
2. Push runs accumulate new history, producing the next peak bootstrap
3. The peak bootstrap is essentially novel each cycle because the *push trajectory* from a given valley state is information-rich (not because the *initial state* is novel)

This means **397's macro-state at valleys is more compact than the peaks data suggests**. The valley bootstrap reachable set is still growing at 10M (472 → unknown at 100M) but is much closer to bounded than the peak set.

Hypothesis worth flagging (not a claim): **a valley-sampled view of 397 might admit a finite-state-plus-counter automaton model** — counter = N_left run length, automaton state = current valley bootstrap. Whether the valley reachable set actually saturates is unresolved at 10M (we'd need 100M for 397 to test, which is wall-time-prohibitive — see notes/15's 2.5M burn calibration).

This refines but does NOT overturn the case-2 verdict. The full dynamics still has unbounded structure at peaks. But the *amount* of unbounded structure may be smaller than implied by the peaks-only view.

### Suspicious symmetry with 531

531's R-bootstrap (peaks AND valleys) showed heavy-tailed structure with top word `(20)` appearing 1252× and a suffix-anchored top-5. **397's valley L-bootstrap shows the same heavy-tailed signature** with top word `∅` and a small common core.

The visual structural signature of "auxiliary state at the *consumption* end of a sweep" looks similar across these two TMs:
* Heavy-tailed frequency
* Short bounded words
* Common core of recurring states
* Suffix-anchored (531) or prefix-anchored (397) extension structure

Whereas the "auxiliary state at the *generation* end of a sweep" (397 peaks) is information-rich, flat-frequency, unique per cycle.

**Possible methodology insight (cross-TM)**: the *peaks vs valleys* axis may be more informative than the *peaks-only* analysis for sweep-PDAs in general. The valley side captures the recurrence backbone; the peak side captures the trajectory novelty.

Whether the bbchallenge Discord has formalized this peaks/valleys-asymmetry framing is unknown to us.

### What `notes/19` got wrong / right

`notes/19` posed Phase 1 as: experiment to discriminate "valley bootstrap saturates" vs "doesn't." That binary missed the subtler answer the 10M data + structural probe actually produce: 397's bootstrap *length* is bounded, the *reachable SET* is not (for any feasible horizon), and the SET grows essentially injectively. 531's behavior is qualitatively different (heavy-tailed, suffix-anchored).

The Phase 1 question "does valley bootstrap saturate?" is the wrong frame for 397 — the right question is "what determines which subset of bounded-length words gets visited?", and the answer involves position-dependent alphabet bias plus prefix-extension dynamics.

For 531 the saturation question IS the right frame and is still open at 10M.

## Addendum (2026-05-27 ~02:30) — 531's R-bootstrap is bimodal (core + excursions)

A targeted probe (`tools/sandbox/bb33_531_alternation_probe.py`) classified each distinct R-bootstrap word at 531 as either:
* `alt`: matches the strict pattern `(12 21)*  [12]?  20` from the top-5
* `rare`: contains a rare symbol from {22, 11, 10}
* `other`: no rare symbols but doesn't match alt
* `empty`: the empty word

Result (peaks at 10M, similar for valleys):

| Class | Distinct | Occurrences |
|---|---|---|
| `empty` | 1 (0.0%) | 3 (0.0%) |
| `alt` | **7 (0.2%)** | **3220 (27.5%)** |
| `rare` | 4523 (99.8%) | 8471 (72.4%) |
| `other` | 0 (0.0%) | 0 (0.0%) |

So **the alternation language is exactly 7 words** at this depth — bounded by k≤6, with strict 12/21 alternation and phase tied to k parity (k=0 → bare `20`, k=1 → starts with 12, k=2 → starts with 21, etc.). These 7 "highway" states account for ~28% of all R-bootstrap occurrences.

The remaining 72% of occurrences are spread across **~4500 distinct "excursion" words containing 22 or 11**. Examples: `(22 11 22)`, `(11 22)`, `(21 22 12 21 11)`. These are short (length 1-5 in the head of the list) and individually rare.

### What this means

531's R-bootstrap is NOT a simple regular language `(12 21)* 20` — that captures only the highway. The full language is **highway + excursions**:

* The highway is finite (7 states) and accounts for the heavy-tailed top of the frequency distribution.
* The excursions are a slowly-growing set (per `notes/20`, novelty ratio 0.40 → slowing) that the system visits when "off the main loop."

If excursions saturate at a bounded set with more data (the 100M burn launched at ~02:00 will tell us), then 531 admits a clean finite-state reduction. If excursions keep slow-growing, then we have a similar story to 397 — bounded individual words but possibly unbounded reachable set.

The 100M burn at sample rate 100 will give ~117k samples (vs 11.7k at 10M). If the excursion count is bounded ~5000-10000, the curve will flatten visibly. If it keeps growing linearly with samples, we have evidence for case 2 (slow but unbounded).

## Honest attribution

Calibrated deliberately, same habit as `notes/20`:

* **Definitely not new to the bbchallenge Discord**: bounded bootstrap length for both holdouts, sweep-PDA structure, the basic distinct-words-grow observation. LegionMammal's abandoned 531 model presumably included some version of the suffix-anchored top-word structure.
* **Probably not new**: the qualitative position-bias finding for 397 (people who looked at trace dumps would have noticed leading-symbol regularity).
* **Possibly new (artifact-level)**: the *quantitative* per-position alphabet table, prefix-determinism percentages, and side-by-side structural comparison. These come from running our specific probe; whether anyone has published these particular numbers is unknown to us.

The contribution remains: **the probe pipeline** (`bb33_bootstrap_structure.py`) is TM-generic and language-agnostic, reusable for any sweep-PDA holdout. Numbers above are reproducible by `bb33_bootstrap_structure.py --in sim/<file>.reversals.json --side <left|right> --kind both`.

## Next steps

1. **100M-loop 531 burn** at sample rate 10 (projected ~80 min wall time). Would tell us whether the R-bootstrap reachable set actually saturates or keeps slow-growing.
2. **Word-language classification probe**: are 531's R-bootstrap words a regular language (DFA-recognizable)? A morphic / substitutive sequence? The suffix-anchored top structure is suggestive.
3. **Lean refinement**: a *refined* WilyCoyote SweepPDA realization could use the empirical structure — `MacroCfg := (leftN : ℕ) × (rightBoot : RightBootWord)` where `RightBootWord` is constrained by the observed length bound + alphabet — *without* committing to a particular reachable-set hypothesis.
4. **Compare to 397 valleys** — we only probed 397 peaks. The valleys (`<right B, 11>`, `<right B, 21>`) had distinct-counts 472 and 549 at 10M; structurally different head positions, would be worth a side-by-side.

## Files

- `tools/sandbox/bb33_bootstrap_structure.py` — generic structural probe (length, alphabet, position-bias, prefix-determinism, periodicity, extension tests)
- Run on existing data files: `sim/397_burn_10M_v2.reversals.json`, `sim/531_burn_10M.reversals.json` (both from `notes/20`)
