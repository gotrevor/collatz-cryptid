# Fat Coyote (397) — Lean Scaffold (Phase 0) 🪤

Started 2026-05-26. First Lean encoding of holdout 397 (Fat Coyote).
Deliberately matches `Collatz.Holdout153`'s minimal shape (Machine +
TM-level Hypothesis), *not* `Collatz.Bigfoot`'s full stack (Machine +
Dynamics + Encoding + Reduction + Classification).

## What landed

```
lean/Collatz/FatCoyote/
├── Machine.lean      — TM transition table, `Collatz.FatCoyote.machine`
└── Hypothesis.lean   — `Hypothesis : Prop := BB.NeverHalts machine Cfg.blank`

lean/Collatz/FatCoyote.lean    — module-level export
lean/Collatz.lean              — adds `import Collatz.FatCoyote`
```

`lake build` clean (3313 jobs). Adds 0 sorries.

## Why no Dynamics.lean

`notes/15` calibrated the case split for "Fat Coyote admits a clean
parametric reduction":

| Shape | Probability |
|---|---|
| Bigfoot-style 3-counter (a, b, c) | 15% |
| Bounded counter automaton (more state than 3 ints) | 40% |
| Strictly harder than Bigfoot (unbounded auxiliary) | 35% |
| Other / hybrid | 10% |
| Decisive structural insight not yet found | 5% |

A `Dynamics.lean` for Fat Coyote would commit to one of these shapes.
Committing to (a, b, c) is the over-call that `notes/15` already
retracted. Committing to a bounded-counter-automaton type without the
10M-loop reversal-burn would repeat the same mistake at a coarser grain.

So Phase 1 of the Fat Coyote track is **the experiment**, not the Lean
encoding: extract valley bootstrap words across 10M+ macro-loops at each
of the 7 dominant head signatures, plot the novelty curve, see whether
the reachable set saturates. Estimated ~3-5 hours of CPU per the 2.5M
extrapolation.

## What a Phase 1 Dynamics.lean would look like (if the experiment goes well)

Conditional on valley bootstrap *saturating* at some finite set
`B_sig ⊂ Σ*` per head signature, the right shape is:

```lean
-- Sketch only — DO NOT write until the experiment supports it.
structure MacroCfg where
  headSig    : HeadSig            -- inductive with 7-12 constructors
  rightPower : ℕ                  -- the (P_right)^N_right body
  leftPower  : ℕ                  -- the (P_left)^N_left body
  bootValley : Σ_valley           -- finite valley bootstrap, indexed by headSig
  bootPeak   : List Sym           -- ⚠ unbounded? open question
  cyclePhase : Bool               -- push-run vs pop-run

def macroStep : MacroCfg → MacroCfg := ...

def Hypothesis_dyn : Prop :=
  ∀ n, (macroStep^[n] macroInit).headSig ≠ ...halt-signature...
```

If valley bootstrap *does not* saturate, this shape doesn't typecheck
(no `Σ_valley` finite type). Then the honest move is:

```lean
-- Alternative: encode the sweep-PDA framework, leave bootstrap abstract.
structure SweepPDA where
  alphabet  : Type
  headState : Type
  pushRule  : headState → alphabet → Option (headState × alphabet)
  popRule   : headState → alphabet → Option (headState × alphabet)
  -- ...

-- Fat Coyote IS a sweep PDA, but with unbounded auxiliary state.
-- Non-halting reduces to a configuration-reachability question on
-- the (potentially infinite) PDA — not a finite invariant.
```

This second shape has no Lean-side precedent in collatz-cryptid (or, as
far as we know, in mathlib). Writing it would be a small framework
contribution regardless of whether Fat Coyote turns out decidable.

## What's solid (per `notes/14` + `notes/15`)

These are the empirical facts a Phase 1 Dynamics.lean would *encode*, not
*prove* (they're empirical):

* Fat Coyote is a sweep PDA: 100% of macro-step edits at the right
  boundary of the left-side stack. Confidence ~100%.
* Push and pop runs strictly alternate (1247/1247 over 200k loops).
* Run-length grows linearly at slope 0.5/cycle. R² = 0.9999 at 2.5M loops.
* 12 head states observed, 7 dominant (98%+ of mass).
* Empirically non-halting through 2.5M macro-loops (~7.5M TM-steps).

## Connection to Wily Coyote (531/532)

LegionMammal has a near-complete statistical model of 531 (abandoned).
The naming hierarchy (Wily / Fat) suggests similar sweep-PDA structure
with different period. If a Phase 1 Dynamics encoding lands for Fat
Coyote, it should generalize to Wily with parameter changes only —
worth scoping the shared `SweepPDA` framework with both in mind.

## Honest pitch for continuing

The KB has been chewed on by Trevor + Ren for ~3 days; the 397-specific
empirical work (`notes/10`, `12`, `14`, `15`) is fresh from 2026-05-23/25.
The bbchallenge Discord community has been on these holdouts for years,
in Rocq, with more BB context than we have (per
[[reference-bb-community-uses-rocq]]).

The realistic value of a Lean-side encoding:

1. **Floor**: gives Trevor a concrete artifact to point at when explaining
   "what's in scope" — same way `Collatz.Holdout153` did for 153.
2. **Mid**: if Phase 1 saturation holds, the `SweepPDA` framework would
   be the first Lean encoding of sweep-PDA-style BB analysis. Not a
   breakthrough; a Lean-side first.
3. **Ceiling**: notice something the Rocq community missed. Small but
   non-zero, and deliberately calibrated: see the "Honest attribution"
   sections in `notes/20` and `notes/21`.

## Next steps (in order)

1. **Run the 10M reversal-burn** — `tools/sandbox/bb33_397_burn.py` with
   `--reversal-snapshots` flag (does not exist yet; needs adding).
2. **Plot the valley bootstrap novelty curves per head signature** — does
   the count saturate, grow logarithmically, or grow linearly?
3. **Decide Dynamics.lean shape** based on (2):
   - Saturation → finite-type `Σ_valley`, write the macro-step recurrence.
   - Unbounded → write the abstract `SweepPDA` framework, leave Fat Coyote
     as an instance with `opaque` reachable-bootstrap type.
4. **Write Hypothesis_dyn** at the dynamics level and prove
   `Hypothesis_dyn → Hypothesis` (TM-level non-halt follows from
   dynamics-level non-halt). This is the Bigfoot pattern.
5. **Stop**. Step 4's payoff is conditional on Step 3's experiment.
   Anything past Step 4 (e.g., trying to prove `Hypothesis_dyn` itself)
   is community-research-scale work.
