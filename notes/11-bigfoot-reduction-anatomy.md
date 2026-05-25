# Bigfoot Reduction - Anatomy of the `sorry` 🦴

What the `MachineNeverHalts` theorem in `lean/Collatz/Bigfoot/Hypothesis.lean` actually claims, and what would discharge the `sorry`.

## The statement

```lean
theorem MachineNeverHalts (h : Hypothesis) :
    BB.NeverHalts machine BB.Cfg.blank
```

Unfolding the definitions:
- `Hypothesis := ∀ n : ℕ, Dyn.orbit n ≠ none` - the parametric `(a,b,c)` orbit, starting at `A(2,1,2)`, never reaches the halt branch (`a = 0 ∧ b % 6 = 2`).
- `BB.NeverHalts machine c := ∀ n : ℕ, BB.stepN machine n c ≠ none` - the Bigfoot TM, starting from blank tape, never halts.

So the theorem says: **if the abstract `(a,b,c)` dynamics doesn't halt, then the concrete TM doesn't halt.**

## What the proof actually needs

Three ingredients:

### 1. The encoding `enc : Dyn → BB.Cfg`

A function that, given an abstract `(a, b, c)` state, produces a concrete TM configuration. For Bigfoot, this maps the triple to a tape pattern:
- `a` counts something like the number of a specific 4-symbol macro-block to the left of the head.
- `b` counts the homogeneous-block size in the sweep target on the right.
- `c` is the phase indicator (the state + a small finite-cell decoration).

Ligocki's blog has the exact recipe. Translating it to Lean is straightforward but tedious: define `enc` as a function that produces the tape via finitely many `Tape.write` operations from `Tape.blank`.

**Status**: not yet written. Concrete and doable, ~30-60 min.

### 2. The bootstrap: `stepN machine 69 Cfg.blank = some (enc Dyn.init)`

After 69 micro-steps from blank tape, the Bigfoot TM enters its first "phase" - a configuration matching `enc (A(2,1,2))`.

**Status**: not yet proved. Two approaches:

- **Symbolic** - 69 steps of `simp [BB.step, machine]` chained, or a custom `decide`-like tactic. Lean's `decide` doesn't work directly because `Tape : ℤ → Sym` isn't decidably equal (no extensionality on infinite functions). But we can reduce to "tapes agree on finitely many positions" via `funext` + case analysis on the position. Tedious but mechanical, ~1-2 hours.

- **Switch the tape representation** - change `Tape` from `ℤ → Sym` to `Finsupp ℤ Sym` (or `AList`). Tapes become decidably equal in the finite-support case. Better engineering long-term; ~1 day refactor.

### 3. The simulation step: one Dyn step ↔ many TM steps

This is the heart of the reduction. For each transition `Dyn.step d = some d'`, there is a number `cost(d) > 0` such that running the TM for `cost(d)` micro-steps from `enc d` reaches `enc d'`:

```lean
∀ (d d' : Dyn), Dyn.step d = some d' →
    ∃ n > 0, BB.stepN machine n (enc d) = some (enc d')
```

For Bigfoot, `cost(d)` is **linear in `b`**: each Dyn-step sweeps through a `b`-sized block and re-encodes the result. The proof is by **case analysis on `b % 6`** (one case per Dyn rule), with each case proved by induction on a "phase counter."

**Status**: the hardest of the three. Probably weeks of part-time work, because:
- Each phase requires a precise tape invariant (what `enc d` looks like before vs. after).
- The induction on `b` requires proving that a "macro step" preserves the encoding for any `b`.
- Lean tactic support for "run the TM for some number of steps and observe" is sparse - we'd need helper lemmas.

## What I can do in a single pass

Convert the monolithic `sorry` into a structured form where:
- The "glue" - going from a `Reduction` interface to the no-halt conclusion - is fully proved (no `sorry`).
- The remaining `sorry` is exactly the three ingredients above, each individually identified.

The glue proof:

```text
Plan:
  By induction on j : ℕ, define a strictly increasing sequence
  N(j) : ℕ with stepN machine (N(j)) Cfg.blank = some (enc (orbit_value j)),
  where orbit_value j is the j-th element of the Dyn orbit
  (well-defined under Hypothesis).

  N(0) = 69 (bootstrap).
  N(j+1) = N(j) + cost(orbit_value j) (simulation step).

  Hence N is unbounded.

  For any target n : ℕ, pick j with N(j) > n. Then
  stepN machine (N(j)) blank ≠ none.
  By Halt-stickiness (lemma: stepN m blank = none → stepN (m+k) blank = none),
  contrapositively stepN n blank ≠ none.
```

After this pass, the diff between "current state" and "Phase D complete" is:

```
(- 1 monolithic sorry +
 + define `enc : Dyn → Cfg`     (~30 min - 1 hr)
 + prove bootstrap (69 steps)    (~1-2 hr or 1-day refactor)
 + prove simulation step          (~weeks)
 + glue proof - DONE ✓)
```

That's the pass.

## Why this matters

The current `sorry` is **opaque**: someone reading the file sees one big "not proved." The structured version is **transparent**: each remaining piece is a labeled mathematical object with an estimable time-cost. Future-Trevor (or future-Ren, or Shawn if he ever helps) can pick up any of the three pieces independently.

This is the same anatomy as PNT+ proofs in Lean - factor the reduction into encoding + simulation + glue, and the glue is often the cheap part.
