# Handoff 🤝

**Last session**: 2026-05-25 evening (Korec stated, 397 over-claim retracted, Bigfoot Python rewrite v1→v4).
**Branch**: `init` (no remote; local-only repo).
**Build**: `cd lean && lake build` — clean, **3 intentional sorries** (Tao, Korec, Bigfoot.sim).

This file is the entry point for any future session picking up this project. Read top to bottom.

## Current state (one-screen view)

```
Phase A (Collatz core)              ✅ Basic, Conjecture, Conditional, OrbitMin   [no sorry]
Tao 2019 framework                  ✅ LogDensity defs + Tao statement            [statement-only sorry]
Korec 1994 framework                ✅ Korec statement inside AlmostAllPos        [statement-only sorry]
BB framework                        ✅ Own BB.lean (not mathlib's TM0)            [no sorry]
Bigfoot reduction interface         ✅ Reduction struct + glue (toNeverHalts)     [no sorry]
Bigfoot encoding                    ✅ bigfootEnc, anchored coords, cell-verified [no sorry]
Bigfoot cost function               ✅ 24·c + 176 (Quick_Sim Diff Rule 0)         [no sorry]
Bigfoot bootstrap                   ✅ stepN 69 blank = some (bigfootEnc init)    [no sorry]
Bigfoot sim                         🚧 PARKED INDEFINITELY                        [sorry; see below]
MachineNeverHalts                   follows from sim once it's done
Bigfoot Python rewrite v1→v4        ✅ literal → macro → super-cycle → dance      (see notes/16)
Holdout 153 reduction               ❌ refuted (4-counter conjecture)
Holdouts 397, 531 (factor complex.) ✅ shape-explosive, bounded factor complexity
531 finite-reachable hypothesis     ❌ refuted (10M-loop saturation)
397 PDA sweep + linear +0.5/cycle   ✅ confirmed at 2.5M loops, R²=0.9999
397 clean (a,b,c) reduction         ❌ refuted (97% unique peak bootstraps; notes/15)
BB(6) batch deciders                ✅ 0/1085 decided (community-known result reproduced)
```

Three intentional sorries in the Lean repo:
1. **`Collatz.tao2019`** in `lean/Collatz/Tao.lean` — statement-only.
2. **`Collatz.korec1994`** in `lean/Collatz/Korec.lean` — statement-only (NEW today).
3. **`Collatz.Bigfoot.bigfootReduction.sim`** in `lean/Collatz/Bigfoot/Reduction.lean` — parked.

## Why `sim` is parked

Trevor's question (2026-05-25): "Would this actually prove anything new?" Answer: **No.** `sim` would be formalization of Ligocki's published reduction (the (a,b,c) parametric dynamics ↔ Bigfoot TM correspondence). Mechanical verification. ~weeks of real Lean work.

The genuinely open question is **`Bigfoot.Hypothesis`** itself — that the (a,b,c) orbit never reaches the halting branch (`a = 0 ∧ b % 6 = 2`). Empirically verified for astronomical iteration counts; mathematically unproven. Proving it would close BB(3,3).

Sim is left as a clearly-typed obligation. The interface, encoding, cost, bootstrap, and glue are all done — sim is the one remaining piece.

## Today's arc (2026-05-25 evening session, in order)

1. **Lean: `Korec 1994` stated.** `Collatz.korec1994` inside `AlmostAllPos` framework — strongest pre-Tao "almost all" result. Proof skeleton documented inline. Commit `d6303ba`.

2. **397 substitution hunt (refuted) → PDA sweep finding.** notes/14 written: 100% boundary edits, 100% strict push/pop alternation across 624 cycles, +0.5/cycle linear growth at R²=0.998.

3. **397 calibration burn.** Streaming Quick_Sim to 2.5M loops (~78 min CPU). Confirms linear growth: slope 0.4992, R²=0.998 push / R²=0.9999 pop. 12 head states locked, no new phenomena. Killed at 2.5M (extrapolated 10M = 5+ hours, diminishing returns).

4. **397 deep inspection refutes clean (a,b,c).** notes/15: 623 sweep-reversal snapshots show peak bootstrap is 97% unique per cycle. The clean 3-counter form from notes/14 doesn't fit. Updated case split: 15% Bigfoot-shaped / 40% bounded counter automaton / 35% strictly harder. Memory `feedback_research_claims_rigor.md` extended with episode 4 (lesson: "different signals need different sample sizes — a 4-sample pattern match isn't a 624-sample regression").

5. **Bigfoot Python rewrite v1→v4** (notes/16). Stepwise decompilation; each version equivalence-checked against v1. v4 surfaces Bigfoot's `(a, b, c)` integer-state signature in raw data: bites are 98.3% zero, non-zero bites form APs within a cycle, N (dance bounce-count) is near-period-10. Commit `8524b3b`.

## Where to start next

The natural next moves, ranked by leverage:

1. **Bigfoot v5: extract closed-form (a, b, c).** Build on notes/16. Two paths:
   - **Tape-parametric**: at super-cycle boundaries, the cells just left of `right_boundary` likely have form `... 0 0 1^a 2 1^b 2 1^c [head] 2 0 0 ...` (placeholder). Read it off directly.
   - **Trigger-based**: each non-zero bite happens when A_skim crosses a `1^k 2` block in the fossil. Identify what creates those blocks during A-passes; the (a,b,c) recurrence falls out from cycle-to-cycle block relationships.
   - If v5 lands the (a, b, c) recurrence, it reproduces Shawn's published reduction in our coordinates — and any (a,b,c) state can be unfolded back to a literal-TM tape via v4 → v3 → v2 → v1.

2. **Apply v1→v4 rewrite series to other holdouts.** 153, 531, 397 — does the same decompilation surface their integer state (if any)? notes/15 already showed 397's bootstrap is 97% unique per cycle, suggesting 397 doesn't reduce to (a,b,c) — but a stepwise v1→vN treatment might still expose the actual state shape.

3. **397 case discrimination (Task #7 pending).** Run Quick_Sim to 10M loops with reversal-aware snapshots; compute valley-bootstrap novelty curves per head signature out to ~30k cycles. If curves flatten → case 2.5 (decidable counter automaton). If keep growing → case 3 (harder than Bigfoot). ~3-5 hours CPU. Discriminating.

4. **Korec proof attempt.** Three-step skeleton documented in `Korec.lean`: trajectory descent → parity-sequence weighted counting → glue. Korec's original is ~5 pages of elementary density bookkeeping; might be tractable.

5. **Lagarias-style stopping time bounds** (further). Some already in `Conditional.lean`. Density of cycles, upper/lower bounds.

Skip:
- Pinging Shawn Ligocki. Trevor protective of the relationship; he'll initiate if appropriate.
- 153 four-counter retry (refuted by trace analysis).
- BB(6) Inductive decider extraction (post-Inductive residue; won't help).
- 100M-loop burns on 397. Trevor's instinct vindicated at 2.5M; further bashing won't beat the wall.

## Repo layout

```
collatz-cryptid/
├── HANDOFF.md                  # this file
├── README.md
├── species.py, stopping.py     # early Collatz exploration (pre-Lean)
├── data/refs/                  # PDF library (Tao, Lagarias, Krasikov-Lagarias)
├── lean/                       # Lean 4.29.1 + mathlib
│   ├── lakefile.toml, lean-toolchain
│   └── Collatz/
│       ├── Basic.lean          # T, sanity
│       ├── Conjecture.lean     # Collatz.Conjecture : Prop
│       ├── Conditional.lean    # no_nontrivial_cycle, τ_ge_log2
│       ├── OrbitMin.lean       # colMin, conjecture_iff_colMin_one
│       ├── LogDensity.lean     # logSum, logProb, HasLogDensity, AlmostAllPos
│       ├── Tao.lean            # Tao 2019 Theorem 1.3 (statement-only sorry)
│       ├── Korec.lean          # Korec 1994 (statement-only sorry; added today)
│       ├── BB.lean             # own 3-state 3-symbol TM framework
│       ├── Bigfoot/
│       │   ├── Machine.lean, Dynamics.lean, Hypothesis.lean
│       │   ├── Encoding.lean   # bigfootEnc + bigfootCost + bootstrap_full
│       │   └── Reduction.lean  # Reduction struct + glue + bigfootReduction (sim sorry)
│       └── Holdout153/
│           ├── Machine.lean, Hypothesis.lean
├── notes/                      # per-topic .md, 01..16
│   ├── 14-holdout-397-pushdown-sweep.md        # PDA confirmed; partial supersession banner
│   ├── 15-holdout-397-pattern-erosion.md       # supersedes notes/14's (a,b,c) claim
│   └── 16-bigfoot-rewrite-series.md            # Python v1→v4 stepwise decompilation
├── sim/                        # Quick_Sim traces, batch CSVs (some .gitignored)
│   ├── 397_burn_500k.* / 397_burn_10M.*       # streaming-burn checkpoints + side files
│   └── 397_reversals.json                      # 623 peak + 623 valley snapshots
└── tools/sandbox/              # project-specific Python
    ├── bb33_397_*.py                          # 9 scripts; see notes/14 and notes/15
    ├── bigfoot_v1_literal.py
    ├── bigfoot_v2_macro.py
    ├── bigfoot_v3_supercycle.py
    └── bigfoot_v4_dance_internals.py
```

## Running things

- **Lean build**: `cd lean && lake build`. ~3s incremental. **3 expected sorry warnings.**
- **Lean check single file**: `lake build Collatz.Korec` (or any specific module).
- **Sandbox scripts**: `sandbox /path/to/tools/sandbox/script.py` (absolute path; the `sandbox` wrapper sources nix env from `~/personal/tools/sandbox/`).
- **Bigfoot Python series**: each VN runs and prints its own self-verification ("PASS" against v1) plus structural observations.
- **Quick_Sim CLI**: `~/.venvs/bb/bin/python ~/src/busy-beaver/Code/Quick_Sim.py [opts] <tm>`. Shawn Ligocki's repo; venv at `~/.venvs/bb` (Python 3.14).
- **Streaming burn on a TM**: `sandbox tools/sandbox/bb33_397_burn.py --max-loops N --out FILE.json`. Writes checkpoints every 500k loops. Per-loop wall-time grows with tape length — at scale of 2-3M loops, total wall-time is ~hours.

## Key references (in `data/refs/`)

| File | Content |
|---|---|
| tao-2019-almost-all-orbits.pdf | arXiv:1909.03562 v5. Headline modern result. |
| lagarias-2003-survey-1.pdf | arXiv:math/0309224 v13. Annotated Bibliography I (1963-1999). 74pp. |
| lagarias-2006-survey-2.pdf | arXiv:math/0608208 v6. Annotated Bibliography II (2000-2009). 42pp. |
| krasikov-lagarias-2003-density.pdf | arXiv:math/0205002. Density bound `x^0.84`. 21pp. |

Index + Tao's conventions for Lean: `notes/refs.md`. Korec 1994 itself NOT in `data/refs/` — referenced via Lagarias surveys, which extensively cite it.

## Conventions & gotchas

### Lean
- `BB.Cfg` has `@[ext]`. Without it, `ext` tactic fails on Cfg equality.
- `set_option maxRecDepth N in theorem` does **not** play well with attached `/-- docstring -/`. Use a regular `-- comment` instead.
- `decide` with `maxRecDepth ≥ 2000` works for `BB.stepN N blank` projections (state, pos, tape at specific i) up to N ≈ 69. Tape equality on `ℤ → Sym` is **not** decidable; needs `funext` + position case split.
- `Real.logb` lives in `Mathlib.Analysis.SpecialFunctions.Log.Base`, not `Log.Basic`.
- Cross-checking via `decide`/`#eval` on small projections catches encoding bugs early.

### Git
- Branch `init`; no remote. HANDOFF earlier claimed a pre-commit hook blocks trailing whitespace / CRLF / `main` commits, but no such hook is installed at `.git/hooks/pre-commit` — commits succeed regardless. Still good practice to keep files clean.
- `.gitignore` excludes `lean/.lake/` (build cache, ~7GB) and the 50k/200k-loop complexity traces (~800MB).
- Commit message convention: short prefix, technical body. Co-Authored-By tag for Claude-generated commits.

### Python rewrite chain (Bigfoot)
- Every `bigfoot_v*.py` defines an equivalence check against `BigfootV1` (the canonical literal simulator). Run any version and it prints `verification: PASS -- ok` if its macros match v1's micros bit-exact.
- v4 imports v3 imports v2 imports v1. Each version is callable standalone for analysis.
- If you write v5/v6/..., follow the same pattern: subclass the previous version, override at a higher granularity, add a `verify_v*_against_v1` function, and print its result on `main()`.

### Quick_Sim macro rules for Bigfoot (Diff Rule 0, used for `bigfootCost`)
```
Initial: 00^inf 12^(a+1) 11^(b+7) <A (11) 11^(c+1) 00^inf
Diff:    00^inf 12^0    11^-6   <A (11) 11^8       00^inf
Steps:   24·c + 176, Loops: 27
```
Exact for `b ≥ 7`. Below threshold, micro-step counts vary per case.

## Behavioral notes (Trevor)

- **Don't suggest pinging Shawn Ligocki.** Explicit pushback. Reason: protective of relationship.
- **Honestly distinguish formalization from new math.** Lead with what's novel vs. what's reproduction.
- **Negative results are clean information.** 531 saturation refuted, 397 (a,b,c) refuted — document honestly, don't bury.
- **Calibrate before claiming structure.** A bounded-X finding from a 200k-sample window needs ≥1-2 orders of magnitude more sampling before naming it structural. Different signals need different sample sizes — a 4-sample pattern match isn't a 624-sample regression.
- **Trace-back-to-canonical matters.** Each Python rewrite version VN includes a verifier against v1. Don't break that chain.

---

🌯 Wrapped 2026-05-25 evening (Bigfoot v4 + Korec + 397 retraction).
