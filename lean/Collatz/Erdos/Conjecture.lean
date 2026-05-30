import Mathlib.Data.Nat.Digits.Defs

/-!
# Erdős's conjecture on base-3 digits of `2^n` (1979)

> For every `n > 8`, the base-3 representation of `2^n` contains the digit `2`.

Equivalently: for `n > 8`, `2^n` is **not** a sum of distinct powers of 3
(since `digits 3 (2^n) ⊆ {0,1}` would express `2^n` as such a sum).

The known exceptional `n` (where `digits 3 (2^n) ⊆ {0,1}`) are `n ∈ {0, 2, 8}`,
giving `2^n ∈ {1, 4, 256}` with base-3 representations `[1]`, `[1,1]`,
and `[1,1,1,0,0,1]` respectively.

This is open. We package it as a `Prop` so partial results can take it as a
hypothesis (and so we can state Prop-level relationships with Collatz).
-/

namespace Collatz.Erdos

/-- **Erdős, 1979**. For all `n > 8`, the base-3 representation of `2^n`
contains a digit `2`. -/
def ErdosConjecture : Prop :=
  ∀ n : ℕ, 8 < n → 2 ∈ Nat.digits 3 (2 ^ n)

/-- The complementary "no-2-in-base-3" predicate on a natural. -/
def NoTwoInBase3 (n : ℕ) : Prop := 2 ∉ Nat.digits 3 n

/-- Reformulation: Erdős says the only `2^n` with no `2` in base 3 lie
in the (eventually empty) initial segment `n ≤ 8`. -/
theorem erdos_iff :
    ErdosConjecture ↔ ∀ n : ℕ, NoTwoInBase3 (2 ^ n) → n ≤ 8 := by
  unfold ErdosConjecture NoTwoInBase3
  constructor
  · intro h n hn
    by_contra hgt
    exact hn (h n (Nat.lt_of_not_le hgt))
  · intro h n hn
    by_contra hno
    exact Nat.not_lt.mpr (h n hno) hn

end Collatz.Erdos
