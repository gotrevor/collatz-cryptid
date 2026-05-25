# Handoff 🤝

**Last session**: 2026-05-25 afternoon (Lean Bigfoot bootstrap + Tao 2019 statement + PDF library).
**Branch**: `init` (no remote; local-only repo).
**Build**: `cd lean && lake build` - clean, 2 intentional sorries (see below).

This file is the entry point for any future session picking up this project. Read top to bottom.

## Current state (one-screen view)

```
Phase A (Collatz core)              ✅ Basic, Conjecture, Conditional, OrbitMin   [no sorry]
Tao 2019 framework                  ✅ LogDensity defs + Tao statement            [statement-only sorry]
BB framework                        ✅ Own BB.lean (not mathlib's TM0)            [no sorry]
Bigfoot reduction interface         ✅ Reduction struct + glue (toNeverHalts)     [no sorry]
Bigfoot encoding                    ✅ bigfootEnc, anchored coords, cell-verified [no sorry]
Bigfoot cost function               ✅ 24·c + 176 (Quick_Sim Diff Rule 0)         [no sorry]
Bigfoot bootstrap                   ✅ stepN 69 blank = some (bigfootEnc init)    [no sorry]
Bigfoot sim                         🚧 PARKED INDEFINITELY                        [sorry; see below]
MachineNeverHalts                   follows from sim once it's done
Holdout 153 reduction               ❌ refuted (4-counter conjecture)
Holdouts 397, 531 structure         ✅ shape-explosive, bounded factor complexity
531 finite-reachable hypothesis     ❌ refuted (10M-loop saturation)
BB(6) batch deciders                ✅ 0/1085 decided (community-known result reproduced)
```

Only two sorries remain in the repo:
1. **`Collatz.Bigfoot.bigfootReduction.sim`** in `lean/Collatz/Bigfoot/Reduction.lean` - parked.
2. **`Collatz.tao2019`** in `lean/Collatz/Tao.lean` - statement-only, intentional.

## Why `sim` is parked

Trevor's question (2026-05-25): "Would this actually prove anything new?"

Answer: **No.** `sim` would be formalization of Ligocki's published reduction (the (a,b,c) parametric dynamics ↔ Bigfoot TM correspondence). Mechanical verification. ~weeks of real Lean work. Modest community value as scaffolding for Lean-BB formalization, parallel to busycoq's BB(5) Coq formalization.

The genuinely open question is **`Bigfoot.Hypothesis`** itself - that the (a,b,c) orbit never reaches the halting branch (`a = 0 ∧ b % 6 = 2`). Empirically verified for astronomical iteration counts; mathematically unproven. Proving it would close BB(3,3). No known approach.

So `sim` is left as a clearly-typed obligation that any future contributor can pick up. The interface, encoding, cost, bootstrap, and glue are all done - sim is the one remaining piece. About `cost`: I picked `24·c + 176` from Quick_Sim's `Diff Rule 0`, which is exact for `b ≥ 7`. Small-b initial steps may need a correction (additive constant). Surfaces when sim is tackled.

## Where to start next

The natural next moves, ranked by leverage:

1. **Korec-style "almost all" results in the new framework**. Tao 2019 supersedes Korec, but Korec's natural-density result (`Colmin(N) ≤ N^θ` for `θ > log₂(3)/2 ≈ 0.79`) is much more accessible and would be a real proved theorem inside the `AlmostAllPos` / `HasLogDensity` infrastructure we set up. Likely mathlib-worthy.
2. **Lagarias-style stopping time bounds**. Classical results - some already partly in `Conditional.lean` (e.g., `τ_ge_log2`). Extend to upper/lower bounds, density of cycles, etc.
3. **More of Tao's defined notions** (Syracuse map, Krasikov-Lagarias `x^0.84` density). Build up the formal infrastructure of modern Collatz around Tao's paper.
4. **397 substitution hunt** (Python side). Test if `snapshot[t+1] = σ(snapshot[t])` for finite substitution σ. Possibly cheap, possibly informative.
5. **`sim` proof** (Lean side, parked). Real ~weeks of work. Formalization, not new math.

Skip:
- Pinging Shawn Ligocki. Trevor protective of the relationship; he'll initiate if appropriate.
- 153 four-counter retry (refuted by trace analysis).
- BB(6) Inductive decider extraction (post-Inductive residue; won't help).

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
│       ├── BB.lean             # own 3-state 3-symbol TM framework
│       ├── Bigfoot/
│       │   ├── Machine.lean, Dynamics.lean, Hypothesis.lean
│       │   ├── Encoding.lean   # bigfootEnc + bigfootCost + bootstrap_full
│       │   └── Reduction.lean  # Reduction struct + glue + bigfootReduction (sim sorry)
│       └── Holdout153/
│           ├── Machine.lean, Hypothesis.lean
├── notes/                      # per-topic .md, numbered 01..13 + refs.md
├── sim/                        # Quick_Sim traces, batch CSVs (some .gitignored as large)
└── tools/sandbox/              # project-specific Python (bb33_*, bb6_*, h153_analyze)
```

## Running things

- **Lean build**: `cd lean && lake build`. ~3s incremental, ~5min cold (mathlib). Two expected sorry warnings.
- **Lean check single file**: `lake build Collatz.Tao` (or any specific module).
- **Sandbox scripts**: `sandbox /path/to/tools/sandbox/script.py` (absolute path; the `sandbox` wrapper sources nix env from `~/personal/tools/sandbox/`).
- **Busy-beaver Python tooling**: `~/.venvs/bb/bin/python ~/src/busy-beaver/Code/Quick_Sim.py [opts] <tm>`. Shawn Ligocki's repo; venv at `~/.venvs/bb` (Python 3.14).

## Key references (in `data/refs/`)

| File | Content |
|---|---|
| tao-2019-almost-all-orbits.pdf | arXiv:1909.03562 v5. The headline modern result. |
| lagarias-2003-survey-1.pdf | arXiv:math/0309224 v13. Annotated Bibliography I (1963-1999). 74pp. |
| lagarias-2006-survey-2.pdf | arXiv:math/0608208 v6. Annotated Bibliography II (2000-2009). 42pp. |
| krasikov-lagarias-2003-density.pdf | arXiv:math/0205002. Density bound `x^0.84`. 21pp. |

Index + Tao's conventions for Lean: `notes/refs.md`.

## Conventions & gotchas

### Lean
- `BB.Cfg` has `@[ext]` (added today). Without it, `ext` tactic fails on Cfg equality.
- `set_option maxRecDepth N in theorem` does **not** play well with attached `/-- docstring -/`. Use a regular `-- comment` instead.
- `decide` with `maxRecDepth ≥ 2000` works for `BB.stepN N blank` projections (state, pos, tape at specific i) up to N ≈ 69. Tape equality on `ℤ → Sym` is **not** decidable; needs `funext` + position case split.
- Cross-checking via `decide`/`#eval` on small projections catches encoding bugs early. Did this today; caught the anchor-position-offset bug.

### Git
- Branch `init`; no remote. Pre-commit hook blocks commits to `main` AND blocks trailing whitespace / CRLF / trailing blank lines.
- Strip CRLF: `tr -d '\r' < file > file.tmp && mv file.tmp file`. Strip trailing blank lines: `awk 'BEGIN{lines=""} {lines = lines $0 "\n"} END {sub(/(\n[[:space:]]*)+$/, "", lines); printf "%s\n", lines}' file > file.tmp && mv file.tmp file`. Busy-beaver Quick_Sim output is the common offender.
- `.gitignore` excludes `lean/.lake/` (build cache, ~7GB) and the 50k/200k-loop complexity traces (~800MB).

### Quick_Sim macro rules for Bigfoot (Diff Rule 0, used for `bigfootCost`)
```
Initial: 00^inf 12^(a+1) 11^(b+7) <A (11) 11^(c+1) 00^inf
Diff:    00^inf 12^0    11^-6   <A (11) 11^8       00^inf
Steps:   24·c + 176, Loops: 27
```
Exact for `b ≥ 7`. Below threshold, micro-step counts vary per case.

## Behavioral notes (Trevor)

- **Don't suggest pinging Shawn Ligocki.** Explicit pushback. Reason: protective of relationship, doesn't want to abuse. Saved as memory `feedback_no_shawn_pings.md`.
- **Honestly distinguish formalization from new math.** When suggesting next steps, lead with what's novel vs. what's reproduction. Today's `sim` parking was the right call once we examined what it would prove.
- **Negative results are clean information.** Today's 531 saturation refuted yesterday's hypothesis. Trevor wanted that documented honestly, not buried.
- **Calibrate before claiming structure.** A bounded-X finding from a 200k-sample window needs at least 1-2 orders of magnitude more sampling before naming it structural.

---

🌯 Wrapped 2026-05-25 13:02 EDT.
