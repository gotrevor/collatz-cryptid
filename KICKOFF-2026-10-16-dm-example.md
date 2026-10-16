# KICKOFF 2026-10-16 (lane 4): Dubickas-Mossinghoff's example from Akiyama; floor = translated ceiling

Target file: `lean/Collatz/Antihydra/AkiyamaDubickas.lean`.  Everything above the last section is
proved (see `HANDOFF-akiyama-43.md`); the last section has 5 `sorry`s.  Statements were checked by
hand and numerically (q ≤ 8, x < 3000, 12 steps).

## Targets, in order (commit after each)

1. `dmStops_mono` - unfold `DMStops`; a witness `k` for `T` works for `S`.
2. `dmStops_zero_top_of_minWord_ne_maxWord` - `{0, q - 1} ⊆ (Finset.range q).erase 1` when `q ≥ 3`;
   then `dmStops_ne_zero_iff_ne_one` (its second conjunct, read right to left, after rewriting by the
   first) and `dmStops_mono`.
3. `next_sub_eq_floorNext_sub`, `digit_sub_eq` - arithmetic: `next q y = y + ⌈y/q⌉`, and
   `⌈(x - (q-1))/q⌉ = x / q`; `omega` with `Nat.div_add_mod` / `Nat.mod_lt`, or unfold `digit`/`next`.
4. `iterate_next_sub_eq` - induction on `k`; `floorNext q x ≥ x` keeps the hypothesis `q - 1 ≤ ·`.

## Rules

Do not change any statement or definition except to fix a genuine mis-statement - then stop and
explain in the handoff instead.  No `native_decide`, no new axioms; `decide` is fine.  Lines ≤ 100
chars.  Finish with `#print axioms` of every theorem in the file recorded in the handoff.  Do not edit
other files.  Handoff: `HANDOFF-dm-example.md`.
