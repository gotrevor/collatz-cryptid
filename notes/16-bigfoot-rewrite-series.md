# Bigfoot Stepwise Decompilation: v1 → v4 🔬

Pedagogical decompilation of the Bigfoot Turing machine through a series of Python rewrites. Each version is equivalence-checked against the previous (and ultimately against `v1`, the canonical literal 9-rule simulator). Goal: surface logical structure without changing what the program computes.

**Motivating question** (Trevor, 2026-05-25): "Why can't I just write it in Python and logically deduce what it's doing?" Short answer: because deducing infinite-horizon behavior of a TM requires an *invariant*, not just a simulator. But you can use the rewrite process to *find* candidate invariants by stages.

## Method

Each version VN+1 is a refactoring of VN that:
- Defines higher-level operations on top of VN's primitives.
- Includes a verifier (`verify_against_v1`) that runs VN+1 alongside `BigfootV1` and aborts on any tape/state/position divergence.
- Reveals structure that was hidden in the previous version's granularity.

If a later version V_K ever reaches a closed-form (a, b, c)-style recurrence, **every intermediate version remains executable and equivalence-checked**, so any (a, b, c) state can be unfolded back to a literal-TM configuration.

## v1 — Literal TM (`bigfoot_v1_literal.py`)

Dead-simple: 9-rule transition table, sparse tape (`defaultdict(int)`), single-cell `.step()`. The reference semantics.

The transition table:
```
         0      1      2
    A | 1RB    2RA    1LC
    B | 2LC    1RB    2RB
    C | ---    2LA    1LA
```

Halt condition: `C` on `0` (the only `---` in the table). The entire halting question reduces to: **does the head ever land in state C reading a 0?**

After 10,000 micro-steps from blank tape: head at position +88, state A, tape spans [-13, 104] (118 nonzero cells). Not halted.

## v2 — Macro-step (`bigfoot_v2_macro.py`)

Collapses the rule table's two "skim loops" into single macro-operations:

```
A_skim_right: while reading 1 -> write 2, move right; loop.
              Terminate when reading 0 (write 1, move right, enter B)
              or reading 2 (write 1, move left, enter C).

B_skim_right: while reading 1 or 2 -> leave unchanged, move right; loop.
              Terminate when reading 0 (write 2, move left, enter C).

C_step: one micro-step (swap 1<->2, move left, enter A; or HALT on 0).
```

**Verification**: `verify_against_v1` runs 5000 macro-steps in lockstep with v1's micro-steps; PASS at every boundary.

**Observations**:
- Micro/macro compression is exactly **2.0×** over 10k and 100k macros. Each macro is on average 2 micro-steps. Not by design — it's a property of Bigfoot dynamics.
- The first four B_skim_right lengths are **1, 3, 5, 7** — clean linear growth in successive B-sweeps. Hints at a counter.

## v3 — Super-cycle (`bigfoot_v3_supercycle.py`)

One super-cycle = one (A↔C dance) + one (B-sweep). The dance is the time the head spends in the left "fossil record" between B-sweeps. v3 records per-super-cycle stats:
- `dance_macros`, `dance_micros`
- `b_sweep_micros`
- `right_boundary` (rightmost nonzero cell)

**Verification**: PASS at every super-cycle boundary against v1, for 200 super-cycles.

**Observations**:
- `b_sweep_micros` (200 cycles): `3, 5, 7, 9, 1, 13, 1, 17, 1, 21, 1, 1, 27, 1, 1, 1, 35, 1, 1, 1, 1, 1, 47, 1, 1, 1, 1, 1, 1, 61, ...` Two classes: "big" sweeps (3, 5, 7, 9, 13, 17, 21, 27, 35, 47, 61, ...) growing super-linearly, and "trivial" sweeps of length 1 (head bounced into B with a 0 already adjacent).
- 99% of all micro-steps go into the dance, 1% into B-sweeps.
- `right_boundary` grows by 1 or 2 per super-cycle, pattern `1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, ...`
- The Collatz-shape fingerprint is now visible: big-sweeps are "x3+1 rollovers", trivial-sweeps are "x/2 deferrals". Exactly the cadence of an integer-counter system going through carry chains.

## v4 — Dance internals (`bigfoot_v4_dance_internals.py`)

Hypothesis from staring at v3's numbers: every dance has structure

```
dance = (C_step, A_skim) repeated N+1 times
     = N "bounces" + 1 "drop"

bounce = (C_step, A_skim ending on 2 -> re-enters C)
drop   = (C_step, A_skim ending on 0 -> enters B -> ends dance)
```

Each (C_step, A_skim) pair has a **bite count** = number of 1s eaten by the A_skim before bouncing or dropping. Bites ≥ 0.

**Verification**: PASS at every super-cycle boundary, 200 cycles.

**Observations** (300 super-cycles, 73,493 total dance steps):

1. **Bites are extraordinarily sparse**: **98.3% of dance steps have bites=0.** A typical dance is just "C-step, A-bounces-immediately-on-2, C-step, A-bounces-immediately-on-2, ..." for hundreds of bounces.

2. **Non-zero bites form arithmetic progressions within a single cycle**:
   - cycle 19 non-zero bites: `7, 9, 11` (AP with common diff 2)
   - cycle 21 non-zero bites: `23, 25, 27` (AP with diff 2)
   - cycle 22 non-zero bites: `30, 34, 38` (AP with diff 4)
   - cycle 25 non-zero bites: `10, 14, 18` (AP with diff 4)

3. **The N sequence (bounces per dance) is near-period-10**:
   - cycles 31-39: `3, 18, 27, 42, 51, 66, 75, 90, 99`
   - cycles 41-49: `3, 18, 27, 42, 51, 66, 75, 90, 99` — identical
   - cycle 40: `113`. cycle 50: `114` — drift by 1 across the period.
   - Within the period: alternating `+15, +9, +15, +9, +15, +9, +15, +9` increments.

## The (a, b, c) signature, in our coordinates

Three nested layers of integer state:

| Level | What it measures | Cadence |
|---|---|---|
| **Inner** | bite count of a single A_skim | mostly 0; occasionally non-zero |
| **Middle** | AP of non-zero bites within a cycle (common difference, length) | once per super-cycle |
| **Outer** | N (bounce count) sequence, near-period-10 with slow drift | every 10 super-cycles |

This is **Bigfoot's `(a, b, c)` recurrence visible in raw data, before any algebraic reduction**. Shawn Ligocki's reduction maps each super-cycle boundary's tape to three integers; we've made the same three integers visible by stepwise decompilation of the simulator.

What we have NOT done: extracted the closed-form mapping `(a, b, c) -> (a', b', c')` from one super-cycle to the next. That requires either reading off the tape parametric form directly (v5), or matching our `(N, bite-AP, drift)` triple to Shawn's published formulas.

## v5 — Open

Two paths forward, either of which would land the (a, b, c) form:

**Path A: tape-parametric.** At each super-cycle boundary, the tape's region just left of `right_boundary` has a specific parametric form. Read it off:

```
... 0 0 1^a 2 1^b 2 1^c [head] 2 0 0 ...   # candidate form (placeholder)
```

If the form is correct, `(a, b, c)` is right there.

**Path B: trigger-based.** Each non-zero bite happens when the A_skim crosses a `1^k 2` block in the fossil. Find what causes those blocks to form during previous A-passes, and the (a, b, c) recurrence falls out as the relationship between consecutive cycles' block-structures.

## What the rewrite series demonstrated

The simulator IS the rules; running it tells you nothing about whether the head ever lands on `(C, 0)`. But **stepwise refactoring of the simulator surfaces structure**. By v4 we can see Bigfoot's `(a, b, c)` integer state without an explicit invariant — just by changing the granularity at which we describe execution.

This is what "unraveling the state machine in Python" actually buys you: not a proof of halting/non-halting, but a clean parametric form that *makes the halting question stateable*. Bigfoot.Hypothesis is "the `(a, b, c)` orbit never satisfies the halt condition." Without v1→v4-style refactoring, you don't have a clean `(a, b, c)` to state the conjecture in terms of.

The same approach applied to 397 (per `notes/15`) shows 397's auxiliary state does NOT reduce as cleanly — the "bootstrap" word is unique 97% of the time at sweep peaks, suggesting more than 3 integers of state. So **the rewrite technique works AND it discriminates between holdouts**: Bigfoot has a clean (a, b, c), 397 likely doesn't.

## Files

| File | Granularity | Verifies against |
|---|---|---|
| `bigfoot_v1_literal.py` | one micro-step | (canonical) |
| `bigfoot_v2_macro.py` | A_skim / B_skim / C_step | v1 |
| `bigfoot_v3_supercycle.py` | dance + B_sweep | v1 |
| `bigfoot_v4_dance_internals.py` | (C, A) pairs with bite counts | v1 |

## Reproducibility

```bash
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_v1_literal.py
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_v2_macro.py
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_v3_supercycle.py
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_v4_dance_internals.py
```

Each VN prints a verification result ("PASS" against v1) plus structural observations as printed text. No additional config or data files needed.
