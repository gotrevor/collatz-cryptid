# DIRECTION (track t4-haar-rate, branch `wip/t4-haar-rate`)

## CURRENT DIRECTIVE (2026-10-17, review lap 3)

**Single objective.**  Advance the crux of `haarRate_le_eight_twentyfifths`: an `L^{1+s}` bound for
the density of Fornet's iid law `μ_p`, p = (18,6,1)/25, s = 1/32 (`MomentBounded`).  Its linear
sufficient form is `CrossEnergyBounded` (C1).  Nothing else on this track is open.

**Mandated next moves, in order.**
1. Lean: state the minimal hypothesis.  `ShiftMomentBounded ⇔ MomentBounded`, and the headline from
   `MomentBounded`.  Then `CrossEnergyBounded ⇒ ShiftMomentBounded` (Jensen) records that (C1) is
   only sufficient.
2. Lean: the integer shift recursion `crossEnergy p N = crossShift p N 1`, which makes (C1) an
   elementary statement about an explicit kernel on positive integers.
3. Crux attack on (C1) through the Fourier/odd-even recursion (notes/37 §8): test the sufficient
   condition (S), uniform smallness of `F_n` at dyadic frequencies, numerically first.  Then try
   to prove it.

**Forbidden drift.**  Polishing Theorem B, new side species, docs-only laps, re-deriving the
equivalent forms of (C1) already in notes/37 §3 and §8.

**Why.**  Laps 1–2 closed on-path leaves (Theorems A/B in Lean).  The crux saw only numerics.  Lap 3
found that the crux is at least as hard as absolute continuity of a near-critical 2-adic
self-similar measure (dimension 1.02); in the real line the analogue is open.  So the next laps
must either find an arithmetic mechanism specific to the 2-adic/integer structure, or record a
sharp obstruction.  Whatever happens, it must happen on the crux.

**Stop rule.**  The kickoff's done condition (target 2 green, target 1 reduced to a precise
obstruction) is met.  If a lap ends with no viable mechanism for (S) or (C1), record the obstruction
and signal `box done` rather than grinding side leaves.

## Directive history
- 2026-10-17 lap 3 (review): set the crux as the only objective, state the minimal hypothesis
  (`MomentBounded`), and attack (C1) through condition (S).  Added a stop rule.

## Standing charter
Kickoff: `KICKOFF-2026-10-17-t4-haar-rate.md`.  Goal: `a_* ≤ c < 1/3` via Fornet's iid law.
New-math lane: conditional results are fine, and a sharp negative counts as a result.
