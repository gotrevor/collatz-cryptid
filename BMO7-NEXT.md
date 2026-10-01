# BMO#7: prove `beaver_math_olympiad_problem_7` 🦫

**Objective:** close the single `sorry` in `lean/Collatz/BMO/Problem7.lean`.
**Do not change** the headline statement.  It is transcribed from the BMO wiki in
formal-conjectures style, and it is the anchor for an upstream `formal_proof` link.  The sanity
`example` must stay too.

**This is a known result.**  Read the written proof first:
`papers/pomme-de-terre-2025-bmo7-proof.md` (summary, credit, and one imprecision to fix), then the
4-page PDF beside it, `papers/pomme-de-terre-2025-bmo7-proof.pdf` (a symlink into
`~/personal/papers/`).

## Suggested route

1. `hf ▸` reduce to the executable `f`, and show `a = seq` by induction.
2. `f` facts: `f n = n + 2` when `v₂(n+1)` is odd, `n + 1` otherwise.  Use `f^[k+1] x = f^[k] (f x)`
   and `f^[k+1] x = f (f^[k] x)` (`Function.iterate_succ_apply`, `Function.iterate_succ_apply'`).
3. Define the target set `S k := v₂ k = 1 ∨ higheven k ∨ (4 < k ∧ higheven (k - 4))` and an
   explicit successor `next` on `S`.  The PDF's three cases give it: from a higheven `k`, the
   next elements are `k+2, k+4, k+6`; from `k` with `k + 2` higheven, the next is `k + 2`; from
   `v₂ k = 1` with neither `k ± 2` higheven, the next is `k + 4`.
4. The invariant is over pairs.  For `n ≥ 4`: `b (n-1)` and `b n` are consecutive in `S`, and
   `b n = f^[n+1] (b (n-1) / 2) - 1`.  Prove the step from `(b (n-1), b n)` to `(b n, b (n+1))`.
   The PDF's induction silently uses the predecessor fact, so make it explicit.
5. Base cases: compute `seq 0 … seq 11` with `decide +kernel` (or `native_decide`, which is fine).
6. Every element of `S` is even, so `a n = b n + 1` is odd.  The cases `n ≤ 3` come from the base
   table.

Lemmas on `padicValNat 2` you will want: `v₂(2m) = v₂ m + 1`, `v₂` of an odd number is `0`, and
"if `v₂ x = v₂ y = j` then `v₂ (x + y) > j`" for the `k ± 2` and `k ± 4` steps.  Factoring a
`v2_add_pow` helper early pays off.

Commit each green checkpoint.  Split into named lemmas and add `sorry` leaves freely; a higher
sorry count during decomposition is progress.
