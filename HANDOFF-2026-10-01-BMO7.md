# Handoff: BMO#7 (2026-10-01)

- Branch `init`.  The proof is in commit 4899543.
- DONE: `Collatz.BMO.Problem7.beaver_math_olympiad_problem_7` is proved with no `sorry`.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.  `lake build` is green.
  The headline statement and the sanity `example` are unchanged.
- The proof: the pair invariant `inv` on `(p, next p)` with `S p`, plus the pair-step lemma `step`
  (orbit merge in 1 to 3 steps).  Details are in the status section of `BMO7-NEXT.md`.
- Next (optional): silence the `show` style-linter warnings in Problem7, and link the proof
  upstream as `formal_proof` (formal-conjectures).  The other repo `sorry`s (Korec, Tao,
  Bigfoot) are designated-open and were not touched.
