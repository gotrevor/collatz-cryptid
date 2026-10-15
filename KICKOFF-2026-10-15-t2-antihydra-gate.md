# KICKOFF 2026-10-15: T2, a Theorem S for Antihydra (rounding-choice foils)

Source: `tmp/context/crossreview.md` §1, §4, §5 "T2".  Antihydra: `a ↦ a + ⌊a/2⌋` from `a = 8`, counter
`+2` on even `a`, `−1` on odd `a`, halt when the counter goes negative (check the exact convention
against `notes/29-bb-collatz-brief-2026-09-23.md` and `notes/30-antihydra-baker-check-2026-09-24.md`
before stating anything).  This is the amusical lane's Theorem R/S pattern exported: a foil family that
shares every structural property and contains both halting and non-halting members.

## Targets, in order

1. **Define the family.**  `F^H_L`: maps equal to `H` except that at odd `x`, each block of `L`
   consecutive odd values chooses `⌊3x/2⌋` or `⌈3x/2⌉` (exact even branch, defect ≤ 1).  Write it in
   Lean (new module `lean/Collatz/Antihydra/Foils.lean`), with Antihydra the all-floor member.
2. **Lean: `exists_halting_member`.**  For every `L`, some member halts from the Antihydra start.
   Idea: at odd `x` pick the odd image; the counter falls and the orbit's blocks are each decided once
   past `x > 2L`.  Commit the statement first.  If a member that provably never halts is also easy
   (always pick the even image when possible?), prove that too: both behaviours in one family.
3. **Classification (paper, sourced).**  Go through every published partial result on Antihydra the
   repo's notes cite (mfornet's inventory: run-length caps, Matveev junctions, `count/log → ∞`, and
   any others), and for each say whether it uses anything beyond "exact even branch, defect ≤ 1".  Each
   that does not holds for every member, so it cannot decide Antihydra.  This is the deliverable the
   community would recognise; open the sources, cite file paths or URLs, mark anything recalled.
4. **The ceiling.**  State the exact ceiling of rounding-blind arguments, as Theorem S did for ray
   joins (`c* = log_{4/3} 3` there).

## Rules

No `native_decide`, no new axioms; Lean lines ≤ 100 chars; commit after each proved target; write
`notes/33-antihydra-foils-2026-10-15.md` as you go (claims tagged Lean / paper / computed, with
confidence).  Do not edit other notes.  Do not commit `tmp/`.  Handoff: `HANDOFF-t2-antihydra-gate.md`.
