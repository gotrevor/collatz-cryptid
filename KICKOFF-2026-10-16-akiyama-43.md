# KICKOFF 2026-10-16 (lane 3): the whole base-4/3 Dubickas problem, plus general shift/scale

Target file: `lean/Collatz/Antihydra/AkiyamaDubickas.lean`.  The first part of the file is proved
(see `HANDOFF-akiyama.md`); the two new sections at the end are stated with `sorry`.  All statements
were checked by hand and numerically.  Reuse the existing private lemmas (`digit_succ_of_ne_zero`,
`digit_eq_zero_iff`, `digit_double_eq_one_iff`, `next_double_of_digit_ne_one`, ...) freely.

## Targets, in order (commit after each)

1. `shift_add`, `minWord_shift_add` - generalize `shift`: if `c ≤ digit q y` then
   `digit q (y + c) = digit q y - c` and `next q (y + c) = next q y + c`, because
   `(q+1)(y+c) + (d-c) = (q+1)y + d + q*c`.  Induction on `k`.
2. `scale`, `minWord_scale` - if `m * digit q y < q` then `digit q (m*y) = m * digit q y` and
   `next q (m*y) = m * next q y` (`(q+1)(m y) + m d = m((q+1) y + d)`, divisible by `q`).
   Note `q = 0` makes the hypothesis vacuous only when `n = 0`.
3. `dvd_next_of_dvd_digit` - `q * next q x = (q+1) * x + digit q x` (from `digit_spec`), and
   `m ∣ q + 1` gives `Nat.Coprime m q`.
4. `dmStops_empty`, `not_dmStops_range` (seed `1`), `dmStops_singleton` - if the residue stays `r < q`
   for all `k`, the digit `a` is constant and `q * (x_{k+1} + a) = (q+1) * (x_k + a)`, so
   `x_k + a = (q+1)^k (x_0 + a) / q^k` and `q^k ∣ x_0 + a` for every `k` (use coprimality), impossible
   for `x_0 + a > 0` (take `k` with `q^k > x_0 + a`).  `r ≥ q` stops at `k = 0`.
5. `dmStops_ne_two_iff_ne_one` - `→`: given `y > 0`, apply the hypothesis to `2y` and `halving`.
   `←`: given `x > 0`, if residue `x % 3 = 2` stop at `k = 0`; else `digit 3 x ≠ 1`, so
   `next 3 x = 2 * y` with `y > 0` (`next 3 x ≥ x`), and `halving` turns "y meets digit 2" into
   "2y meets digit 1"; shift the index by one.  Bridge residue `2` ↔ digit `1` (`omega`).
6. `dm43_pair_iff` - the three two-element subsets of `range 3` are `range.erase 0/1/2`; use
   `dmStops_ne_zero_iff_ne_one` and target 5.  A `Finset.card_eq_two` case split works.
7. `dm43_classification` - cards `0`, `1`, `2`, `3` (`Finset.card_eq_zero/one`, `S = range 3` from
   `Finset.eq_of_subset_of_card_le`).

## Rules

Do not change any statement or definition except to fix a genuine mis-statement - then stop and
explain in the handoff instead.  No `native_decide`, no new axioms; `decide` is fine.  Lines ≤ 100
chars.  Finish with `#print axioms` of every theorem in the file recorded in the handoff (expect only
`propext`, `Classical.choice`, `Quot.sound`).  Do not edit other files.  Handoff:
`HANDOFF-akiyama-43.md`.
