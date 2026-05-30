import Mathlib
import Collatz.Erdos.Basic
import Collatz.Erdos.Partial

/-!
# Low base-3 digits of `2^n`: the provable half of "2 vs 3"

This is the **provable** side of the seam (the open side is
`Axioms.FurstenbergDigitStiffness`).

The lowest base-3 digit already splits Erdős cleanly:
* **odd `n`**: `2^n % 3 = 2`, so the low digit is `2` — `Partial.erdos_odd`. **Done.**
* **even `n`**: `2^n % 3 = 1`, so the low digit is `1`; a `2` must appear among the
  **high** digits.  This is the entire open content (normality / Furstenberg).

More is provable about the *low* digits, and it underwrites Erdős's
"finitely many exceptions" heuristic quantitatively:

`2` is a **primitive root mod `3^k`** — it generates the cyclic unit group
`(ℤ/3^kℤ)ˣ` of order `φ(3^k) = 2·3^{k-1}`.  So as `n` runs over a period,
`2^n mod 3^k` hits **every** unit exactly once: the low `k` digits of `2^n` are
*perfectly equidistributed* over the units.  The units whose base-3 digits avoid
`2` number exactly `2^{k-1}` (last digit must be `1`, the other `k-1` digits in
`{0,1}`), so the 2-free density is

  `2^{k-1} / (2·3^{k-1}) = ½·(2/3)^{k-1}  ⟶ 0`,

the geometric decay behind "only finitely many `2^n` are digit-2-free".

The general primitive-root claim is the classical lifting theorem (`2` is a
primitive root mod `3` and mod `9`, hence mod every `3^k`).

**Update (cap retired):** this is now proved for **all `k`** in `Lifting.lean` as
`orderOf_two_mod_three_pow : orderOf (2 : ZMod (3^k)) = 2·3^{k-1}` (k ≥ 1), via an
elementary LTE witness (`v₃(2^{2·3^j} − 1) = j+1` exactly) and the order endgame —
axiom-clean, no `multiplicity` API.  The `k ≤ 4` `decide` checks below remain as
concrete witnesses (and the 2-free-density `decide`s still cap at `k ≤ 4`; only the
primitive-root half is now general).  The trend `2^{k-1} = 1,2,4,8` matches the
table in `erdos_lowdigit.py`.
-/

namespace Collatz.Erdos

/-- Powers of two are always units mod `3^k` (so `2^n mod 3^k ∈ (ℤ/3^kℤ)ˣ`). -/
theorem two_pow_coprime_three_pow (n k : ℕ) : Nat.Coprime (2 ^ n) (3 ^ k) := by
  apply Nat.Coprime.pow
  decide

/-- The even case has low digit `1`: `2^n % 3 = 1` for even `n`.  So the low
digit gives **no** help for even `n` — the open part lives in the high digits. -/
theorem two_pow_even_mod_three {n : ℕ} (hn : n % 2 = 0) : 2 ^ n % 3 = 1 := by
  rw [two_pow_mod_three]; simp [hn]

/-! ## `2` is a primitive root mod `3^k` (machine-checked, `k ≤ 4`)

`((range (period)).image (i ↦ 2^i)).card = period` says the first `period`
powers are pairwise distinct; since there are exactly `period = 2·3^{k-1}`
units and all powers are units, they exhaust the unit group. -/

theorem two_primitive_root_mod_3 :
    ((Finset.range 2).image (fun i => (2 ^ i : ZMod 3))).card = 2 := by decide

theorem two_primitive_root_mod_9 :
    ((Finset.range 6).image (fun i => (2 ^ i : ZMod 9))).card = 6 := by decide

theorem two_primitive_root_mod_27 :
    ((Finset.range 18).image (fun i => (2 ^ i : ZMod 27))).card = 18 := by decide

set_option maxRecDepth 100000 in
theorem two_primitive_root_mod_81 :
    ((Finset.range 54).image (fun i => (2 ^ i : ZMod 81))).card = 54 := by decide

/-! ## The 2-free density `½·(2/3)^{k-1}` (machine-checked, `k ≤ 4`)

Over one period of `2^i mod 3^k`, the residues whose base-3 digits avoid `2`
number exactly `2^{k-1}`. -/

/-- Count of `2`-free residues among one full period of `2^i mod 3^k`. -/
def twoFreeOverPeriod (k : ℕ) : ℕ :=
  ((Finset.range (2 * 3 ^ (k - 1))).filter
    (fun i => 2 ∉ Nat.digits 3 (2 ^ i % 3 ^ k))).card

theorem twoFree_k1 : twoFreeOverPeriod 1 = 1 := by decide   -- 2^0
theorem twoFree_k2 : twoFreeOverPeriod 2 = 2 := by decide   -- 2^1
theorem twoFree_k3 : twoFreeOverPeriod 3 = 4 := by decide   -- 2^2
theorem twoFree_k4 : twoFreeOverPeriod 4 = 8 := by decide   -- 2^3

/-- The trend is `2^{k-1}`: the low-digit 2-free count *halves the base* each
step relative to the `3^{k-1}` growth of the unit group, hence the `(2/3)^{k-1}`
decay.  (Stated for the verified range.) -/
theorem twoFree_is_pow_two_pred :
    twoFreeOverPeriod 1 = 2 ^ 0 ∧ twoFreeOverPeriod 2 = 2 ^ 1 ∧
    twoFreeOverPeriod 3 = 2 ^ 2 ∧ twoFreeOverPeriod 4 = 2 ^ 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Collatz.Erdos
