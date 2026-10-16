# KICKOFF 2026-10-16: Antihydra is a rational-base minimal word

Target file: `lean/Collatz/Antihydra/RationalBase.lean` (statements committed, five `sorry`s).
Trevor asked for this in Lean so the connection is obvious to anyone who looks: Antihydra's parity
word is the bit-complement of the Akiyama-Frougny-Sakarovitch minimal word in base `3/2` with seed
`rep 7 = 2122` (Andrieu-Eliahou-Vivion, arXiv:2510.11723, Section 1).  Checked numerically for
2,000 terms; the file docstring explains the bridge `H (D + 1) = ⌈3D/2⌉ + 1`.

## Targets, in order (commit after each)

1. `antihydra_value_eq` - induction on `k` with `Foils.orbit_succ`; the step's first coordinate
   ignores the counter.
2. `isMinWord_ceilStep` - the core.  Suggested lemmas: `rep_child` (`q * M = p * N + a`, `a < p`,
   `0 < N` ⇒ `rep p q M = rep p q N ++ [a]`), its converse (`rep p q N ++ [a] ∈ Lang` ⇒ such an `M`
   exists, via `repRevAux` peeling the last digit), then induction on `l` for the prefix property and
   for lexicographic minimality: at `D` the admissible digits in base `3/2` are exactly
   `a < 3` with `2 ∣ 3D + a`, the least is `D % 2`.
3. `isMinWord_unique` - prefixes are determined (two minimal words have equal prefixes by trichotomy
   of `List.lt` on equal-length lists).
4. `antihydra_parity_complement_minWord` - from 1, 2 and `rep_three_two_seven`.
5. `rep_eval` - the statement-audit identity; induction via `repRevAux`.

## Rules

Do not change any statement or definition in `RationalBase.lean` except to fix a genuine
mis-statement - and then stop and write why in the handoff instead of proving the new version.
No `native_decide`, no new axioms; `decide` is fine.  Lean lines ≤ 100 chars.  Finish with
`#print axioms antihydra_parity_complement_minWord` (expect only `propext`, `Classical.choice`,
`Quot.sound`) recorded in the handoff.  Do not edit other files' proofs.  Handoff:
`HANDOFF-afs-minword.md`.
