# Handoff 2026-10-01: BMO#9 done

Branch `init`, HEAD `e94a178` (plus this doc).

## Done
- `BMO9.beaver_math_olympiad_problem_9` (lean/Collatz/BMO/Problem9.lean) proved; statement unchanged.
- Port of ccz181078's Rocq proof (busycoq `verify/BMO9.v`, all modules except TM1) in
  `lean/Collatz/BMO/Problem9/*.lean` (28 files). `Bridge.lean` replaces TM1: the stream recursion
  `x_rec` simulates `Prefix.Exec` without hitting the halting prefix.
- `lean/Collatz/BMO/` sorry-free; `lake build Collatz` green.
- `#print axioms`: propext, Classical.choice, Quot.sound + 6 native_decide axioms
  (CheckTable.{P16,bank_checked,finite_check}, WordCheck.{finite_bounds,finite_check},
  WordLibrary.bank_checked).
- Convention vs Rocq: levels/depths/exponents are ℕ; Prop names capitalised.

## Next (optional)
- Try `decide +kernel` for the six finite checks to drop native_decide (likely slow).
- Comparator harness / upstream `formal_proof` link for BMO#9 (see Comparator/ for #3,#4,#7).
- Remaining repo sorries (Tao, Korec, Bigfoot/Reduction) are out of this run's scope.
