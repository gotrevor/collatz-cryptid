# KICKOFF 2026-10-16: Akiyama's conjecture = Dubickas's problem in bases (q+1)/q

Target file: `lean/Collatz/Antihydra/AkiyamaDubickas.lean` (statements committed; `sorry`s remain).
These are new elementary lemmas found numerically (shift lemma checked for x < 10⁵ in base 4/3 and
x < 3·10⁴ in 5/4, 6/5; min = max until the first 0 checked for 2·10⁴ seeds).  The docstring states
the mathematics.

## Targets, in order (commit after each)

1. `digit_spec`, `maxDigit_spec`, `next_eq_ceil` - arithmetic on `x % q`.
2. `shift` - induction on `k`.  Key step: `digit q x = a ≥ 1` ⇒ `digit q (x+1) = a - 1` and
   `next q (x+1) = next q x + 1` (because `(q+1)(x+1) + (a-1) = (q+1)x + a + q`).
3. `avoidsZero_iff` - from `shift` plus the digit relation; for `→` note seed `x+1` digits are the
   seed-`x` digits minus one; for `←`, `x + 1` with all digits `≤ q - 2` gives `x` digits `+1`
   (prove a reverse shift, or argue by the first index where one side fails).
4. `minWord_eq_maxWord_iff` - when the minimal digit is nonzero, `maxDigit = digit` and
   `maxNext = next`; `maxDigit` is never `0`.
5. `dmStops_ne_zero_iff_ne_one` - residue `0` ⇔ digit `0`; residue `1` ⇔ digit `q - 1` (q ≥ 2);
   seed `1` has digit `q - 1` at step 0, so positive seeds shift correctly.
6. `halving` (base 4/3) - digits in `{0, 2}` keep the value even and halve to digits `{0, 1}`.

## Rules

Do not change any statement or definition except to fix a genuine mis-statement - then stop and
explain in the handoff instead.  No `native_decide`, no new axioms; `decide` is fine.  Lines ≤ 100
chars.  Finish with `#print axioms` of every theorem in the file recorded in the handoff (expect only
`propext`, `Classical.choice`, `Quot.sound`).  Do not edit other files.  Handoff: `HANDOFF-akiyama.md`.
