import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Collatz.Erdos.Conjecture
import Collatz.Erdos.Lagarias

/-!
# Carry-aware base-3 split of `2^N` via Lagarias

Splitting the base-3 representation of any natural `N` at position `k`:

  `2 ∈ digits_3(N)`  ↔  `2 ∈ digits_3(N mod 3^k)`  ∨  `2 ∈ digits_3(N / 3^k)`.

Composed with Lagarias's `2^{σ_k(m)} · σ^k(m) = 3^k · m + S_k(m)`, this
gives the **carry-aware Erdős reformulation**: for any odd `m` reaching
`1` in `k` Syracuse steps,

  `2^{σ_k(m)}` has no `2` in base 3
       ↔
  `S_k(m) mod 3^k` has no `2`
   ∧  `m + ⌊S_k(m) / 3^k⌋` has no `2`.

The reformulation does not prove Erdős — it restates it — but the
constraints it imposes are sharp.

## Why "linear independence of 2 and 3" sits underneath

`3^k m + S_k(m)` resists simplification precisely because 2 and 3 are
**multiplicatively independent** (`log₂ 3 ∉ ℚ`).  No reduction of `3^k`
to a power of 2 exists, so the base-3 digits of `2^N` carry irreducible
information about the joint 2-adic / 3-adic structure of `N`.  Both
Collatz and Erdős's conjecture live in this gap.
-/

namespace Collatz.Erdos

/-- `N % 3^{k+1} = N % 3 + 3 · ((N / 3) % 3^k)`. -/
theorem mod_three_pow_succ (N k : ℕ) :
    N % 3 ^ (k + 1) = N % 3 + 3 * ((N / 3) % 3 ^ k) := by
  set q := N / 3
  set r := N % 3
  set Q := q / 3 ^ k
  set R := q % 3 ^ k
  have hq_decomp : q = 3 ^ k * Q + R := (Nat.div_add_mod q (3 ^ k)).symm
  have hNr : N = 3 * q + r := (Nat.div_add_mod N 3).symm
  have h_lt_R : R < 3 ^ k := Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))
  have h_lt_r : r < 3 := Nat.mod_lt _ (by decide)
  have h3pow : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
  have hN_form : N = 3 ^ (k + 1) * Q + (r + 3 * R) := by
    rw [hNr, hq_decomp, h3pow]; ring
  have hbound : r + 3 * R < 3 ^ (k + 1) := by rw [h3pow]; omega
  rw [hN_form]
  rw [show (3 ^ (k + 1) * Q + (r + 3 * R)) = ((r + 3 * R) + 3 ^ (k + 1) * Q) from by ring]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]

/-- `N / 3^{k+1} = (N / 3) / 3^k`. -/
theorem div_three_pow_succ (N k : ℕ) :
    N / 3 ^ (k + 1) = (N / 3) / 3 ^ k := by
  rw [pow_succ, mul_comm, ← Nat.div_div_eq_div_mul]

/-- The carry-aware base-3 split for the "has a 2" predicate. -/
theorem two_in_digits_three_split (N k : ℕ) :
    2 ∈ Nat.digits 3 N ↔
      2 ∈ Nat.digits 3 (N % 3 ^ k) ∨ 2 ∈ Nat.digits 3 (N / 3 ^ k) := by
  induction k generalizing N with
  | zero =>
    simp [pow_zero, Nat.mod_one, Nat.div_one, Nat.digits_zero]
  | succ k ih =>
    by_cases hN : N = 0
    · subst hN
      simp [Nat.digits_zero, Nat.zero_mod, Nat.zero_div]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      rw [Nat.digits_def' (by decide : 2 ≤ 3) hNpos]
      rw [List.mem_cons, ih (N / 3)]
      rw [mod_three_pow_succ, div_three_pow_succ]
      by_cases hzero : N % 3 + 3 * ((N / 3) % 3 ^ k) = 0
      · have hN3 : N % 3 = 0 := by omega
        have hrest : (N / 3) % 3 ^ k = 0 := by omega
        rw [hzero, hN3, hrest]
        simp [Nat.digits_zero]
      · have h_lt : N % 3 < 3 := Nat.mod_lt _ (by decide)
        have hor : N % 3 ≠ 0 ∨ (N / 3) % 3 ^ k ≠ 0 := by
          rcases Nat.eq_zero_or_pos (N % 3) with h | h
          · right; intro h'; rw [h, h'] at hzero; simp at hzero
          · left; omega
        rw [Nat.digits_add 3 (by decide) _ _ h_lt hor, List.mem_cons]
        tauto

/-- **Carry-aware Lagarias split** (unconditional).

For any `m, k`, decomposing the Lagarias identity gives
`2^{σ_k(m)} · σ^k(m) = 3^k · (m + ⌊S_k/3^k⌋) + (S_k mod 3^k)`, so the
"`2` appears" predicate factors into low-`k`-digit and high-digit
pieces. -/
theorem two_in_digits_lagarias (m k : ℕ) :
    2 ∈ Nat.digits 3 (2 ^ syracuseSigma m k * syracuse^[k] m)
      ↔ 2 ∈ Nat.digits 3 (lagariasS m k % 3 ^ k)
         ∨ 2 ∈ Nat.digits 3 (m + lagariasS m k / 3 ^ k) := by
  have hpos : 0 < (3 : ℕ) ^ k := Nat.pos_of_ne_zero (by positivity)
  have hL : 2 ^ syracuseSigma m k * syracuse^[k] m = 3 ^ k * m + lagariasS m k :=
    syracuse_lagarias m k
  rw [hL, two_in_digits_three_split _ k]
  have hmod : (3 ^ k * m + lagariasS m k) % 3 ^ k = lagariasS m k % 3 ^ k := by
    rw [show (3 ^ k * m + lagariasS m k) = lagariasS m k + 3 ^ k * m from by ring,
        Nat.add_mul_mod_self_left]
  have hdiv : (3 ^ k * m + lagariasS m k) / 3 ^ k = m + lagariasS m k / 3 ^ k := by
    rw [show (3 ^ k * m + lagariasS m k) = lagariasS m k + 3 ^ k * m from by ring,
        Nat.add_mul_div_left _ _ hpos, Nat.add_comm]
  rw [hmod, hdiv]

/-- **Carry-aware Erdős reformulation** (reach-1 specialization).

If odd `m` reaches `1` in `k` Syracuse steps with cumulative halvings
`N = σ_k(m)`, then `2^N` has no `2` in base 3 iff *both*

  * `S_k(m) mod 3^k` has no `2` in base 3, and
  * `m + ⌊S_k(m) / 3^k⌋` has no `2` in base 3.

This is the proper bridge between Erdős's conjecture and Collatz
parity-vector data. -/
theorem no_two_iff_split_of_reach_one {m k : ℕ} (h : syracuse^[k] m = 1) :
    NoTwoInBase3 (2 ^ syracuseSigma m k)
      ↔ NoTwoInBase3 (lagariasS m k % 3 ^ k)
         ∧ NoTwoInBase3 (m + lagariasS m k / 3 ^ k) := by
  have := two_in_digits_lagarias m k
  rw [h, mul_one] at this
  unfold NoTwoInBase3
  rw [this]
  tauto

/-! ## Spot-check on the two known witnesses.

For `(m, k) = (1, 1)`: `S_1(1) = 1`, `3^1 = 3`.  `S_1 mod 3 = 1`,
`⌊S_1/3⌋ = 0`, `m + 0 = 1`.  Both `1` and `1` have no `2` in base 3.
So `2^{σ_1(1)} = 2^2 = 4` has no `2` in base 3.

For `(m, k) = (85, 1)`: `S_1(85) = 1`, `3^1 = 3`.  `S_1 mod 3 = 1`,
`⌊S_1/3⌋ = 0`, `m + 0 = 85 = [1,1,0,0,1]` (base 3).  Both have no `2`.
So `2^8 = 256` has no `2`. -/

example : NoTwoInBase3 (lagariasS 85 1 % 3 ^ 1)
        ∧ NoTwoInBase3 (85 + lagariasS 85 1 / 3 ^ 1) := by
  refine ⟨?_, ?_⟩ <;> (unfold NoTwoInBase3; decide)

end Collatz.Erdos
