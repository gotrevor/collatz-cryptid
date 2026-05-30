import Collatz.BB

/-!
# Sweep-PDA framework for BB(3,3) holdouts

A *sweep PDA* is a Turing machine whose tape evolution, when projected
through Quick_Sim macro-loops with appropriate block size, decomposes
into strictly alternating push/pop runs at the right boundary of a
left-side stack. Per `notes/14`, BB(3,3) holdouts 397 (Fat Coyote)
and 531 (Wily Coyote) are both observed to be sweep PDAs.

## Scope

This file gives the **vocabulary** for stating sweep-PDA-level non-halt
hypotheses. It does NOT prove that any specific TM is a sweep PDA —
that is an empirical observation backed by `notes/14`, `notes/15`,
`notes/20`, not a Lean theorem.

The 10M-loop bootstrap analysis (`notes/20`) confirmed for 397 that the
reachable auxiliary state is unbounded — the valley novelty ratio went
*up* from 0.83 at 200k loops to 1.38 at 10M, ruling out the saturation
hypothesis. The `SweepPDA` structure here uses an **opaque** macro-
configuration type, so it accommodates both bounded-reachable-state
machines (like 531, which has a 1-word saturated left-side bootstrap)
and unbounded ones (like 397).

## What this is good for

* A clean statement-level home for sweep-PDA non-halt hypotheses
  parallel to `BB.NeverHalts`.
* A target for future refinement: a `RefinedSweepPDA` extending this
  with explicit phase tracking, head signature, and run-length structure
  would let us state and prove the empirically-observed invariants
  (per `notes/14`: 100% boundary-edit locality, strict push/pop
  alternation, slope-0.5 run-length growth).

## What this is *not*

* Not a proof that 397 or 531 is a sweep PDA — the empirical evidence
  for that lives in `notes/14`.
* Not a parametric reduction — by design. The 10M data rules out the
  finite-state-counter shape for 397.
* Not a community-novel concept. Sweep PDAs are a well-known structural
  pattern in the bbchallenge Discord; the contribution here is a *Lean*
  encoding of the abstraction, since the BB community works in Rocq.
-/

namespace BB.SweepPDA

/-- Phase of a sweep cycle: the head is currently moving right (pushing
onto the left-side stack) or moving left (popping). -/
inductive Phase | Push | Pop
  deriving DecidableEq, Inhabited, Repr

/-- An abstract sweep-PDA realization of a dynamical system.

The `MacroCfg` type is intentionally opaque; concrete realizations
choose whether it is finite, polynomially-bounded, or unbounded based
on the empirical structure of the underlying machine. For Fat Coyote
this is necessarily unbounded (per `notes/20`); for Wily Coyote the
LEFT-side bootstrap is saturated at 1 word so a refined version could
expose finite state there. -/
structure _root_.BB.SweepPDA where
  /-- Abstract macro-configuration type. -/
  MacroCfg : Type
  /-- One macro-step. Returns `none` if the underlying TM halts. -/
  step : MacroCfg → Option MacroCfg
  /-- Starting configuration. -/
  init : MacroCfg

end BB.SweepPDA

namespace BB.SweepPDA

/-- Iterate `step` `n` times starting from `init`. -/
def orbit (S : BB.SweepPDA) : ℕ → Option S.MacroCfg
  | 0 => some S.init
  | n + 1 => (orbit S n).bind S.step

/-- The sweep-PDA-level non-halting hypothesis. -/
def NeverHalts (S : BB.SweepPDA) : Prop :=
  ∀ n, S.orbit n ≠ none

end BB.SweepPDA
