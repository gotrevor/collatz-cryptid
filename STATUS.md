# STATUS -- collatz-cryptid, track t4-haar-rate 📊
**Haar-mean base-3/2 digit rate `a_* ≤ 8/25 < 1/3`, conditional on one density bound** ·
**Build**: 🟢 green (8706 jobs) · **Updated**: lap 4 · 2026-10-17 · `886eefa`+

(This branch hosts one track; other tracks keep their own HANDOFF files.)

## Where it stands
`haarRate_le_eight_twentyfifths` (`lean/Collatz/Antihydra/HaarDigitRate.lean`) proves
`a_* ≤ 8/25` in finite form from `CrossEnergyBounded candidate`.  There are no `sorry`s and no
axioms beyond the trust base.  The hypothesis is the crux.  It implies an `L^{1+s}` bound on the
density of a near-critical 2-adic self-similar measure, whose real-line analogue (absolute
continuity at an algebraic parameter) is open.

## What's happened (newest first)
- 2026-10-17 lap 4: the crux in residue-free and parity form (`HaarShift.lean`:
  `crossEnergyBounded_iff_parity`, `crossEnergy_add_sub_le`).  The numerics for (S) show slow
  decay and no mechanism; obstruction recorded in notes/37 §9.  Stop rule applied.
- 2026-10-17 lap 3 (review): wrote the directive (crux only).  Identified the minimal hypothesis
  (`MomentBounded`, equivalent to bounded shift moments), and the reading of (C1) as absolute
  continuity plus a Diophantine condition at the point 1.  Hardness assessment in notes/37 §8.
- 2026-10-17 lap 2: Theorems A (`moment_bound`) and B (`haarRate_le_of_crossEnergyBounded`) proved;
  `candidate_spineRatio_lt_one` proved.
- 2026-10-17 lap 1: finite core (`V`, Bellman, anchors `sumV_four`, `sumV_eight`), spine reduction
  (notes/37).

## Outstanding
### Short-term
See `PENDING_WORK.md` (top entry) and `DIRECTION.md` CURRENT DIRECTIVE.
### Long-term
(C1) or `MomentBounded candidate (1/32)`.  Stretch goal: `a_* = c*`, which needs (C1) along the
tilted family up to θ*.
### To completion
The track's kickoff condition is met.  "Unconditional" needs the crux.

## Axiom ledger
| headline theorem | claim | `#print axioms` shows | status |
|---|---|---|---|
| `haarRate_le_eight_twentyfifths` | conditional: `CrossEnergyBounded candidate → a_* ≤ 8/25` | propext, Classical.choice, Quot.sound | trust base only; the hypothesis is an open conjecture (🔴, as a hypothesis of a theorem stated conditionally) |
| `haarRate_le_of_crossEnergyBounded` | conditional, any law with `q(s) < 1` | trust base | — |
| `sumV_four`, `sumV_eight` | anchors `2^4 A_4 = 31`, `2^8 A_8 = 936` | propext | `decide` |

Math-axiom count: 0.

## Pointers
Kickoff `KICKOFF-2026-10-17-t4-haar-rate.md` · handoff `HANDOFF-t4-haar-rate.md` ·
`PENDING_WORK.md` · notes/36, notes/37 · directive `DIRECTION.md`.
