# Collatz Cryptid - Lean Formalization 🦄

Lean 4 + mathlib `v4.29.1`. Toolchain matches `~/personal/lean-sandbox` so the
mathlib oleans cache hits without re-downloading.

## Layout

```
lean/
├── lakefile.toml
├── lean-toolchain
├── Collatz.lean                  # top-level aggregator
└── Collatz/
    ├── Basic.lean                # T : ℕ → ℕ, sanity lemmas, trivial cycle
    ├── Conjecture.lean           # Collatz.Conjecture : Prop
    ├── Conditional.lean          # τ, no_nontrivial_cycle, τ_ge_log2 (all ✅)
    ├── BB.lean                   # 3-state 3-symbol TM framework
    ├── Bigfoot.lean              # aggregator
    ├── Bigfoot/
    │   ├── Machine.lean          # Bigfoot TM (bbchallenge 829)
    │   ├── Dynamics.lean         # A(a,b,c) parametric system (Ligocki 2023)
    │   └── Hypothesis.lean       # BigfootHypothesis + reduction theorem (🚧)
    ├── Holdout153.lean           # aggregator
    └── Holdout153/
        ├── Machine.lean          # Holdout 153 TM (bbchallenge)
        └── Hypothesis.lean       # TM-level non-halting hypothesis
```

## Status

### Collatz proper
| Theorem | File | Status |
|---|---|---|
| `T` sanity lemmas | `Basic` | ✅ |
| `T^[3] 1 = 1` | `Basic` | ✅ |
| `T_iter_τ_eq_one`, `τ_le_of_iter_eq_one` | `Conditional` | ✅ |
| `no_nontrivial_cycle` | `Conditional` | ✅ |
| `τ_ge_log2` | `Conditional` | ✅ |

### BB(3,3) cryptids
| Theorem | File | Status |
|---|---|---|
| `BB` framework (`Machine`, `Cfg`, `step`, `NeverHalts`) | `BB` | ✅ |
| `Bigfoot.machine` (TM definition) | `Bigfoot/Machine` | ✅ |
| `Bigfoot.Dyn.step`, `Dyn.orbit` | `Bigfoot/Dynamics` | ✅ |
| `Bigfoot.Hypothesis : Prop` | `Bigfoot/Hypothesis` | ✅ statable, **not** proved |
| `Bigfoot.MachineNeverHalts` (reduction) | `Bigfoot/Hypothesis` | 🚧 sorry |
| `Holdout153.machine` | `Holdout153/Machine` | ✅ |
| `Holdout153.Hypothesis : Prop` | `Holdout153/Hypothesis` | ✅ statable, **not** proved |

## TM framework choice

Mathlib has `Turing.TM0` but its `Stmt` decomposes write and move into
**separate steps**. Encoding a bbchallenge-style transition like `1RB`
(write 1, move R, state B) in TM0 takes two steps with an intermediate
state, doubling state counts and de-syncing from bbchallenge / Quick_Sim
step counters. We chose to roll a minimal local framework (`Collatz/BB.lean`,
~80 lines) that does read+write+move+transition atomically. Mathlib is
still imported for tactics and lemmas.

## Build

```bash
cd ~/src/collatz-cryptid/lean
lake build
```

Currently 3297 jobs, one warning (the deliberate `sorry` on
`Bigfoot.MachineNeverHalts`).
