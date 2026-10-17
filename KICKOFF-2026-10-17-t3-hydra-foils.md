# KICKOFF 2026-10-17: T3, rounding-choice foils for the whole Hydra schema

T2 (`lean/Collatz/Antihydra/Foils.lean`, `notes/33`) proved, for Antihydra, that halting members of
the rounding-choice family accumulate at the cryptid, so no rounding-blind argument decides it.
`lean/Collatz/Census.lean` already writes Antihydra, int-y1 #323, BB(2,5) Hydra, BBf #218 and Bigfoot
in one schema, int-y1's `Hydra` (`Collatz.Bigfoot.Hydra` in `Bigfoot/Clock.lean`):
`x ↦ p⌊x/q⌋ + g[x mod q]`, walk `y ↦ y + w[x mod q]`, cryptid = "`y ≥ 0` forever".
T3 lifts the T2 gate from one machine to that schema.  New math lane.

Host analysis (2026-10-17, unverified in Lean; check it before relying on it):
- `realize` and the block-uniqueness/density lemmas of `Foils.lean` use only expansion
  (`x' ≥ x + x/2`), so they should hold for any slope `p/q > 1` above a height depending on `p, q, g`.
- The only use of `q = 2` is steering: defect `≤ 1` decides the next parity outright, so a member can
  force an all-odd tail and drain the counter.
- For `q ≥ 3`, a defect-`d` choice reaches only `d + 1` consecutive next residues, starting from a
  residue fixed by the orbit's history.  Sufficient condition for draining: every cyclic window of
  `d + 1` residues mod `q` contains a residue with `w[r] < 0`.  The least such `d` is `d_min`:
  Antihydra 1; #218 (`w = [3, 1, -1]`) 2; Bigfoot in the `X` coordinate (negatives at 14, 17, 23 mod
  24) 14, but several of those residues may be unreachable (`bigfootH` is `0` at multiples of 4).

## Targets, in order

1. **Generic family.**  New module `lean/Collatz/HydraFoils.lean`: the defect-`d` rounding-choice
   family of a `Hydra p q g w` map (choice `τ : ℤ → Fin (d+1)` added to the image), with the
   original map as the all-zero member, and the block-constant subfamily `F_{L,d}` as in T2.  A
   faithfulness anchor: the original map is a member, stated against `Bigfoot.hydraIterate`.
   Commit the statements (with `sorry`) first.
2. **`q = 2` gate.**  For `p ≥ 3`, `q = 2`, `d = 1` and a residue `r` with `w[r] < 0`: halting members
   exist and are dense (agree with the cryptid on any finite set of blocks), as in T2's
   `exists_halting_member` / `halting_dense`.  Instantiate for Antihydra (recover T2's statement via
   `Census.antihydra`; prove the two agree), `Census.hydra323` and `Census.hydraBB25`.
3. **Window gate, `q ≥ 3`.**  The `d_min` window condition above implies halting members are dense,
   for every `p > q ≥ 2`.  Instantiate for `Census.hydra218` with `d = 2`.  For Bigfoot, compute the
   reachable residues of `X mod 24` along the orbit (prove it if a short invariant exists, otherwise
   tag it computed), and state the smallest `d` the condition gives on the reachable set.
4. **Sharpness (paper first, Lean if short).**  For #218 or Antihydra, is `d_min` sharp, i.e. does
   every member with defect `< d_min` keep a rounding-blind lower bound on the walk?  A theorem or a
   counterexample settles it.

Stretch, only after 1-3: the Bigfoot clocked block map (`Clock.lean`, `step4_block`, slope
`256/81`) as the coordinate, and its `d_min`.

## Rules

No `native_decide`, no new axioms; Lean lines ≤ 100 chars; commit after each proved target.  Write
`notes/35-hydra-foils-2026-10-17.md` as you go, claims tagged Lean / paper / computed, with
confidence.  Do not edit other notes or `Foils.lean`'s statements (importing it is fine).  Do not
commit `tmp/`.  Handoff: `HANDOFF-t3-hydra-foils.md`.  Signal `box done` when targets 1-3 are
proved and the note is written; target 4 is a bonus.
