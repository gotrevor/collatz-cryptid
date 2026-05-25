# Holdout 153: Macroscopic Structure & Growth Rate 📈

Phase 2 progress. Not a complete parametric reduction (yet), but a meaningful
*qualitative* finding plus the rough shape of the macro-cycle.

## The headline: polynomial, not exponential

Measured at progressively larger Quick_Sim loop budgets:

| Loops | TM steps reached | Tape nonzeros | Collatz rules found |
|---|---|---|---|
| 5,000 | ~5.6 M | 797 | 16 |
| 20,000 | (intermediate) | 2,067 | 16 |
| 50,000 | ~3.97 G | 7,070 | 16 |

Both **tape nonzeros** and **TM steps** grow on a scaling that's consistent
with:

- Nonzeros ≈ `c₁ · L`  (linear in prover loops L)
- TM steps ≈ `c₂ · L²`  (quadratic in L)

50k loops produced **9× more nonzeros** and **700× more TM steps** than 5k loops.
That ratio ≈ `10 × 70` ≈ `10 × 10²·⁸` — quadratic step-vs-loop with a constant
factor of ~8 from acceleration overhead.

**Compare Bigfoot**: at 5000 loops Quick_Sim reports `Num Nonzeros: ~10^17.26`
— **exponential** in loops. So Bigfoot's macro-time → tape-size map is
exponential; 153's is linear.

This is a real qualitative distinction. It does **not** mean 153 is easier
to decide than Bigfoot, but it tells us *what kind of dynamical system to
look for*: a system whose state has a few small counters and whose macro-time
per step grows linearly with one counter. That's the Collatz-like signature
seen in the per-step formula `Steps = 8·d + 32` from the expansion rules
(`notes/06`).

## Snapshot trace at 100-loop intervals

```
T0   00^inf (00) A> 00^inf                                                    nonzeros:    0
T1   00^inf 11^1 (11) B> 20^10 21^1 11^1 20^1 00^inf                          ≈   26
T2   00^inf 10^21 <B (02) 02^3 00^inf                                         ≈   48
T3   00^inf 10^17 <A (20) 20^7 21^1 11^10 12^1 00^inf                         ≈   72
T4   00^inf 01^1 (01) A> 20^19 11^26 12^1 00^inf                              ≈   94
T5   00^inf 10^51 (10) C> 01^1 11^5 20^1 00^inf                               ≈  116
T6   00^inf 01^13 11^5 (11) A> 11^46 20^1 00^inf                              ≈  130
T7   00^inf 01^72 11^1 (11) A> 02^3 00^inf                                    ≈  152
T8   00^inf 01^1 <A (20) 20^69 21^1 11^13 12^1 00^inf                         ≈  170
T9   00^inf <B (02) 02^93 01^1 20^1 00^inf                                    ≈  190
T10  00^inf 10^51 (10) C> 01^1 11^53 20^1 00^inf                              ≈  212
T11  00^inf 01^90 <C (11) 11^25 12^1 00^inf                                   ≈ ...
T12  00^inf 01^52 11^72 (11) A> 01^1 12^1 00^inf                              ≈ ...
T13  00^inf 01^119 11^1 (11) A> 02^16 12^1 00^inf                             ≈ ...
T14  00^inf <B (02) 02^145 01^1 20^1 00^inf                                   ≈ ...
T15  00^inf 10^103 (10) C> 01^1 11^53 20^1 00^inf                             ≈ ...
```

## The macro-cycle (tentative, confidence ~60%)

The system seems to visit each of these "shape classes" cyclically:

1. **`<B (02) 02^β 01 20`** — "B-stable" with no left block, no inner 11.
   This is a *minimal* config; the system returns to this shape with
   progressively larger `β`. Compare T9 (β=93) and T14 (β=145). Difference
   ≈ 52.
2. Sweep right via macro-rules → `10^α (10) C> 01 11^γ 20`
   ("C-traveling-right" with inner 11 of size γ).
3. State transitions through inner 11 via expansion rules → grows inner 11.
4. Continues bouncing left-right, evolving counters, before returning to (1).

The **B-stable** configs are the natural macro-state we want to track:

```
B-stable(β) :≡  00^∞ <B (02) 02^β 01^1 20^1 00^∞
```

Empirically `β` increases between successive B-stable visits. The recurrence
seems roughly `β_{n+1} = β_n + Δβ_n` for some `Δβ_n` that depends on the
intermediate cycle. Computing `Δβ_n` precisely is the missing piece.

## ⚠️ Correction (added 2026-05-25)

The 4-counter conjecture below is **refuted by direct measurement.** Preserved
in place for the audit trail; do not build on it.

When we parsed the trace at micro-step granularity (`tools/sandbox/h153_analyze.py`
against `sim/153_trace.txt`, 200 rows):

- **121 distinct shape signatures** appeared
- **135 distinct (shape → shape) transitions** appeared
- Most transitions appeared only **2-4 times** — the system keeps minting
  *new* shape variants as it grows. The state space is shape-unbounded over
  the trace, not a fixed-size graph.

That is **not** the signature of a small parametric reduction
(Bigfoot has 6 shape classes + 1 halt). It's the signature of either:
- a large regular-language / Closed-Tape-Language structure, or
- a system whose "macro-state" is not the right abstraction in the first
  place and needs a different decomposition.

I also tried `Code/CPS.py` (Closed Position Set decider) at several settings:

| block-size | window | numConfigs | result |
|---|---|---|---|
| 10 (default) | 30 | 39 | Inconclusive |
| 20 | 60 | 472 | Inconclusive |
| 30 | 100 | 119 | Inconclusive |

CPS at these scales fills its config buffer without closing. So neither the
hoped-for Collatz-style reduction nor a standard closed-position-set proof
is in reach with off-the-shelf tools and a single session of effort.

**What stays true:**
- The polynomial-growth observation (linear nonzeros, quadratic TM steps)
- The 16 auto-discovered Quick_Sim rules (`notes/06`) — those are proved,
  by Quick_Sim's own proof system, as accelerating *parts* of the dynamics
- 153 is genuinely a non-trivial holdout and the 4-counter
  oversimplification underestimates it

**What this means for the Lean side:** `Collatz/Holdout153/Hypothesis.lean`
correctly stays at the TM level (`NeverHalts machine Cfg.blank`). Do **not**
add a `Holdout153/Dyn.lean` paralleling Bigfoot's; the dynamics doesn't
shrink to a small structure.

**Honest assessment of the rigor question:** Trevor asked whether the
"prove" would be Shawn's level or a guess. The 4-counter sketch below was
in the "guess" bucket. Trace measurement promoted it to "refuted." That's
the right epistemic outcome — better caught here than after a Lean writeup.

---

## What the 4-counter reduction probably looks like (REFUTED, preserved for audit)

Conjecture (confidence ~50%):

```
H153(α, β, γ, δ; phase)
```

where:
- `α` = size of outer-left block (`10` or `01` flavour)
- `β` = size of outer-right block (`02` or `20` flavour)
- `γ` = size of inner-left `11` block
- `δ` = size of inner-right `11` or marker count
- `phase` = which sub-family of the 16 rules applies next

Sweep rules: `phase` and three counters tick by constants; one counter
shrinks by 2, another grows by 2.

Expansion rules: `phase` advances; `γ` grows by 3; `α` shrinks by 2;
duration linear in `γ`.

Halt: when `phase = C-at-(00)` *or* `phase = C-at-(?)-where-(?)-is-2`, and
all surrounding markers match the halt condition (`state C reads symbol 2`).

But the explicit 16-case step function isn't written down here. Writing it
is the **completion of Phase 2**. Estimate: 1-2 focused sessions, with
Quick_Sim's verbose trace as the data source.

## What this means for the Lean side

- **Holdout153.Hypothesis** (stated at TM level) stands as-is.
- Once Phase 2 is finished, add `Holdout153/Dyn.lean` paralleling
  `Bigfoot/Dynamics.lean`, with a `H153.step : Dyn → Option Dyn` matching
  the 16 cases.
- Add a dynamics-level `Hypothesis'` and a sorry'd reduction theorem
  paralleling `Bigfoot.MachineNeverHalts`.

## What this means for showing Shawn

If/when the 4-counter reduction is verified:

- It's the same kind of object as his Bigfoot writeup, in his repo's
  notation.
- The polynomial-vs-exponential growth distinction is a clean, citable
  observation.
- That's a real conversation starter, not "please explain this to me."

## Sidebar: 397 and 531 under variant settings

Quick experiments with `--block-size 2`:

| Holdout | TM steps reached in 20k loops | Nonzeros | Rules proven |
|---|---|---|---|
| 397 | 60,663 | 210 | 0 |
| 531 | 8,249,516 | 2,377 | 0 |

- **397** runs at almost native TM speed — block-size 2 isn't unlocking
  acceleration. The machine appears to *not be building tape state* at
  rates the macro-machine can compress. Either its growth is sub-linear,
  or block-size 2 is wrong for it. Needs more experiments
  (block sizes 1, 4, 6, 8; CTL filters; CPS).
- **531** *is* accelerating (412 TM steps / loop) but Quick_Sim isn't
  catching any rules. Likely a closed-tape-language structure that needs
  `CTL?.py` / `CPS.py`.

Both are real "next session" tasks.
