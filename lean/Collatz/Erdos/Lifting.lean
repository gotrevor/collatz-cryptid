import Mathlib

/-!
# Lifting the exponent for `2` modulo powers of `3`

The arithmetic core behind "`2` is a primitive root mod `3^k`": an explicit
2-adic-style witness for the 3-adic valuation of `2^(2·3^k) − 1`.

`two_pow_witness` gives `2^(2·3^k) = 1 + 3^(k+1)·u` with `3 ∤ u`, i.e.
`v₃(2^(2·3^k) − 1) = k+1` **exactly**.  Proved by an elementary binomial
induction (cubing the previous witness), with no `multiplicity`/`emultiplicity`
API.  The two corollaries are the LTE statement in directly usable divisibility
form:

* `three_pow_dvd`     : `3^(k+1) ∣ 2^(2·3^k) − 1`     (the order divides `2·3^k`)
* `not_three_pow_dvd` : `3^(k+2) ∤ 2^(2·3^k) − 1`     (the order is *exactly* `2·3^k`)

This retires, in general `k`, the hardest input to the `k ≤ 4` machine-checked
primitive-root facts in `Equidistribution.lean`.
-/

namespace Collatz.Erdos

/-- **LTE core.** `2^(2·3^k) = 1 + 3^(k+1)·u` for a unit `u` mod `3`
(`v₃(2^(2·3^k) − 1) = k+1` exactly).  Binomial induction: cube the witness. -/
theorem two_pow_witness :
    ∀ k : ℕ, ∃ u : ℤ, ¬ (3 ∣ u) ∧ (2 : ℤ) ^ (2 * 3 ^ k) = 1 + 3 ^ (k + 1) * u
  | 0 => ⟨1, by norm_num, by norm_num⟩
  | (k + 1) => by
      obtain ⟨u, hu, heq⟩ := two_pow_witness k
      refine ⟨u + 3 ^ (k + 1) * u ^ 2 + 3 ^ (2 * k + 1) * u ^ 3, ?_, ?_⟩
      · -- the new witness ≡ u (mod 3), so still a unit
        have hdiff : (3 : ℤ) ∣
            (u + 3 ^ (k + 1) * u ^ 2 + 3 ^ (2 * k + 1) * u ^ 3) - u := by
          refine ⟨3 ^ k * u ^ 2 + 3 ^ (2 * k) * u ^ 3, ?_⟩
          rw [pow_succ, pow_succ]; ring
        intro h
        have h2 := dvd_sub h hdiff
        rw [sub_sub_cancel] at h2
        exact hu h2
      · -- cube the previous equation and re-collect the 3-powers
        have hpow : (2 : ℤ) ^ (2 * 3 ^ (k + 1)) = ((2 : ℤ) ^ (2 * 3 ^ k)) ^ 3 := by
          rw [← pow_mul]; congr 1; rw [pow_succ]; ring
        have e1 : (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
        have e2 : (3 : ℤ) ^ (k + 1 + 1) = 9 * 3 ^ k := by rw [pow_succ, pow_succ]; ring
        have e3 : (3 : ℤ) ^ (2 * k + 1) = 3 * (3 ^ k) ^ 2 := by
          rw [pow_succ, mul_comm 2 k, pow_mul]; ring
        rw [hpow, heq, e1, e2, e3]; ring

/-- `3^(k+1) ∣ 2^(2·3^k) − 1`: the multiplicative order of `2` mod `3^(k+1)`
divides `2·3^k`. -/
theorem three_pow_dvd (k : ℕ) : (3 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ (2 * 3 ^ k) - 1 := by
  obtain ⟨u, _, heq⟩ := two_pow_witness k
  exact ⟨u, by rw [heq]; ring⟩

/-- `3^(k+2) ∤ 2^(2·3^k) − 1`: the order is *exactly* `2·3^k` (not lower mod the
next power of `3`). -/
theorem not_three_pow_dvd (k : ℕ) : ¬ (3 : ℤ) ^ (k + 2) ∣ (2 : ℤ) ^ (2 * 3 ^ k) - 1 := by
  obtain ⟨u, hu, heq⟩ := two_pow_witness k
  rw [heq, add_sub_cancel_left]
  intro h
  apply hu
  rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have hpos : (3 : ℤ) ^ (k + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  rw [hc]; ring

/-! ## From the LTE core to "`2` is a primitive root mod `3^k`" (all `k`)

The order computation that retires the `k ≤ 4` machine-checked cap in
`Equidistribution.lean`. -/

/-- Bridge: a power of `2` is `1` in `ZMod (3^k)` iff `3^k` divides `2^e − 1`. -/
theorem pow_two_eq_one_iff (k e : ℕ) :
    (2 : ZMod (3 ^ k)) ^ e = 1 ↔ (3 : ℤ) ^ k ∣ (2 : ℤ) ^ e - 1 := by
  haveI : NeZero (3 ^ k) := ⟨by positivity⟩
  have hcast : (((2 : ℤ) ^ e - 1 : ℤ) : ZMod (3 ^ k)) = (2 : ZMod (3 ^ k)) ^ e - 1 := by
    push_cast; ring
  rw [← sub_eq_zero, ← hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hnc : ((3 ^ k : ℕ) : ℤ) = (3 : ℤ) ^ k := by push_cast; ring
  rw [hnc]

/-- **`2` is a primitive root mod `3^k` for every `k ≥ 1`**: its multiplicative
order is the full group order `φ(3^k) = 2·3^{k-1}`.  No `k ≤ 4` cap — the proof
runs on the general LTE corollaries (`three_pow_dvd`, `not_three_pow_dvd`) plus the
elementary fact that `2^{odd} ≡ −1 (mod 3)`. -/
theorem orderOf_two_mod_three_pow (k : ℕ) (hk : 1 ≤ k) :
    orderOf (2 : ZMod (3 ^ k)) = 2 * 3 ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  haveI : NeZero (3 ^ (m + 1)) := ⟨by positivity⟩
  simp only [Nat.add_sub_cancel]
  -- order divides `2·3^m`
  have hpow1 : (2 : ZMod (3 ^ (m + 1))) ^ (2 * 3 ^ m) = 1 := by
    rw [pow_two_eq_one_iff]; exact three_pow_dvd m
  have hdvd : orderOf (2 : ZMod (3 ^ (m + 1))) ∣ 2 * 3 ^ m :=
    orderOf_dvd_of_pow_eq_one hpow1
  -- `2^{3^m} ≠ 1` (drop the factor 2): `2^{odd} ≡ −1 (mod 3)`
  have hodd : (2 : ZMod (3 ^ (m + 1))) ^ (3 ^ m) ≠ 1 := by
    rw [ne_eq, pow_two_eq_one_iff]
    intro h
    have h3 : (3 : ℤ) ∣ (2 : ℤ) ^ (3 ^ m) - 1 :=
      (dvd_pow_self (3 : ℤ) (by omega : m + 1 ≠ 0)).trans h
    have hmod : (2 : ℤ) ^ (3 ^ m) - 1 ≡ -2 [ZMOD 3] := by
      have h1 : (2 : ℤ) ≡ -1 [ZMOD 3] := by decide
      have hodd3 : Odd (3 ^ m) := (Odd.pow (by decide : Odd (3 : ℕ)))
      calc (2 : ℤ) ^ (3 ^ m) - 1
          ≡ (-1) ^ (3 ^ m) - 1 [ZMOD 3] := (h1.pow _).sub_right 1
        _ = -2 := by rw [Odd.neg_one_pow hodd3]; ring
    have hz : (2 : ℤ) ^ (3 ^ m) - 1 ≡ 0 [ZMOD 3] := (Int.modEq_zero_iff_dvd).mpr h3
    have : (-2 : ℤ) ≡ 0 [ZMOD 3] := hmod.symm.trans hz
    exact absurd this (by decide)
  -- show `2·3^m ∣ orderOf`, then antisymm
  refine Nat.dvd_antisymm hdvd ?_
  have h2 : 2 ∣ orderOf (2 : ZMod (3 ^ (m + 1))) := by
    by_contra h
    have hcop : Nat.Coprime (orderOf (2 : ZMod (3 ^ (m + 1)))) 2 :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr h).symm
    have hd3 : orderOf (2 : ZMod (3 ^ (m + 1))) ∣ 3 ^ m :=
      hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hdvd)
    exact hodd (orderOf_dvd_iff_pow_eq_one.mp hd3)
  obtain ⟨e, he⟩ := h2
  have he3 : e ∣ 3 ^ m := by
    have hdd : 2 * e ∣ 2 * 3 ^ m := he ▸ hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hdd
  obtain ⟨j, hjm, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp he3
  have hmj : m ≤ j := by
    by_contra hlt
    rw [not_le] at hlt
    have hjm1 : j ≤ m - 1 := by omega
    have hdvd2 : orderOf (2 : ZMod (3 ^ (m + 1))) ∣ 2 * 3 ^ (m - 1) := by
      rw [he]; exact mul_dvd_mul_left 2 (pow_dvd_pow 3 hjm1)
    have hpow2 : (2 : ZMod (3 ^ (m + 1))) ^ (2 * 3 ^ (m - 1)) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hdvd2
    rw [pow_two_eq_one_iff] at hpow2
    apply not_three_pow_dvd (m - 1)
    rwa [show m - 1 + 2 = m + 1 from by omega]
  obtain rfl : j = m := le_antisymm hjm hmj
  rw [he]

end Collatz.Erdos
