# KICKOFF 2026-10-15: T1, Bigfoot's parity clock and a census of shared engines

Source: `tmp/context/crossreview.md` §1, §4, §5 "T1" (cross-lane review; scripts in
`tmp/context/crossreview/`).  NEW mathematics about open problems; nothing here settles Bigfoot.

## Targets, in order

1. **Lean: the parity clock.**  In `lean/Collatz/Bigfoot/` (read `Dynamics.lean` first), state and
   prove `Dyn.parity_clock`: along the `Dyn` orbit, `b_{n+2} ≡ b_n + 1 (mod 2)` (review's form:
   `orbit (n+2) = some s₂ → orbit n = some s₀ → s₂.b % 2 = (s₀.b + 1) % 2`; adapt to the actual
   API, but keep the mathematical content).  Proof sketch: case split on `b mod 6` and
   `c ∈ {2, 3, 5}`, from `e(r, c) ≡ c + 1` and `c ≡ r_prev (mod 2)`.  Commit the statement first,
   then the proof.
2. **The reduced 4-step map.**  Fit the exact clocked form (`b ↦ (256/81)·b + g(b mod 81·?)` or
   whatever is exact) on `10⁵` steps of the real orbit with a known-answer control, then prove it on
   paper and, if it is short, in Lean.  Conclusion to reach: "Bigfoot is a base-3 ×4/3 Hydra driven
   by a 4-phase clock, counter drift +1/6", stated exactly.
3. **Census.**  Lean or exact-script conjugacy lemmas: int-y1 #323's orbit is Antihydra's engine
   `H` started at 2 (`x_{n+1} + 2 = H(x_n + 2)`); Antihydra is `H` from its start.  Settle whether
   BB(2,5) Hydra (`3⌊a/2⌋ + 3`) and Bigfoot's reduced map fit the same schema and with which engine.
   Every map must be checked against a primary source in the repo or `~/src/bb-deep-dive`; mark
   anything recalled.
4. **Gate on `KPosCascade`.**  Is V6's reserve `k` a function of `(clock phase, b mod 3^j)` for small
   `j`?  A collision count decides it.  If yes, `KPosCascade` may be within the horizon; if no, record
   it as the open problem in costume (Maze §0 language).

## Rules

No `native_decide`, no new axioms; Lean lines ≤ 100 chars; commit after each proved target; write a
note `notes/32-bigfoot-clock-2026-10-15.md` as you go (claims tagged Lean / paper / computed, with
confidence).  Do not edit other notes.  Do not commit `tmp/`.  Handoff: `HANDOFF-t1-bigfoot-clock.md`.
Folklore check: if any fact may already be known on the bbchallenge Discord, say so in the note.
