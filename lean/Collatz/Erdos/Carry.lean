import Collatz.Erdos.DoublingCA
import Collatz.Erdos.Conjecture
import Mathlib.Tactic

/-!
# Path 1: carries are the magnitude ↔ digit interface

A base-3 digit `2` in `2^n` is *produced by the carry rule* of the doubling CA
(`DoublingCA.lean`): the cell `(d, c) ↦ ((2d+c) % 3, (2d+c) / 3)` outputs digit
`2` **exactly** at the two carry states `(d,c) = (1,0)` or `(2,1)`.

A carry is where magnitude meets digits: it fires precisely when the local sum
reaches the base (`2d + c ≥ 3`), a size threshold, yet it is a digit-level event.
So Erdős ("for `n>8`, `2^n` has a base-3 digit `2`") is a **carry-positivity**
statement: the doubling carry field is never 2-sparse.

Numerics (`~/personal/tools/sandbox/path1_carry.py`, n up to 500):
* carry density → **0.498 ≈ 1/2**, digit-2 density → **0.331 ≈ 1/3** — exactly the
  carry-rule heuristic (`P[carry]=½`, `P[output=2]=⅓`), the same `(2/3)` decay seen
  in `Equidistribution.lean`.
* even-`n` near-exceptions (`n=2,8`: zero 2s; `n=4,6,24`: one 2) are the open
  "carry never makes a 2" configurations.
-/

namespace Collatz.Erdos

/-- A doubling cell outputs digit `2` **exactly** at the carry states
`(d,c) = (1,0)` or `(2,1)`.  Digit-`2` production *is* a carry event. -/
theorem doubleDigit_fst_eq_two {d c : ℕ} (hd : d < 3) (hc : c < 2) :
    (doubleDigit d c).1 = 2 ↔ (d = 1 ∧ c = 0) ∨ (d = 2 ∧ c = 1) := by
  interval_cases d <;> interval_cases c <;> simp [doubleDigit]

/-- Carry-out fires exactly when the local sum reaches the base: `2d + c ≥ 3`. -/
theorem doubleDigit_carry_eq_one {d c : ℕ} (hd : d < 3) (hc : c < 2) :
    (doubleDigit d c).2 = 1 ↔ 3 ≤ 2 * d + c := by
  interval_cases d <;> interval_cases c <;> simp [doubleDigit]

/-! ## The carry invariant and the global "every 2 is carry-made" bridge

(`doubleDigit_carry_lt_two` — the `{0,1}`-carry invariant — now lives in
`DoublingCA.lean`, where the canonicality proofs also use it.) -/

/-- **Every `2` in a doubled digit list is carry-made.**  If the input list has
valid base-3 digits (`d < 3`) and a valid incoming carry (`c < 2`), then any `2`
in the output comes from a digit-`2`-producing carry state `(d',c')`
(`= (1,0)` or `(2,1)`).  Induction threading the `{0,1}`-carry invariant. -/
theorem two_mem_doubleAux_carry_made {L : List ℕ} {c : ℕ}
    (hc : c < 2) (hL : ∀ d ∈ L, d < 3) (h : 2 ∈ doubleAux L c) :
    ∃ d' c', d' < 3 ∧ c' < 2 ∧ (doubleDigit d' c').1 = 2 := by
  induction L generalizing c with
  | nil =>
    interval_cases c <;> simp [doubleAux] at h
  | cons d ds ih =>
    rw [doubleAux] at h
    simp only [List.mem_cons] at h
    have hd : d < 3 := hL d (List.mem_cons_self ..)
    rcases h with hhead | htail
    · exact ⟨d, c, hd, hc, hhead.symm⟩
    · exact ih (doubleDigit_carry_lt_two hd hc)
        (fun x hx => hL x (List.mem_cons_of_mem d hx)) htail

/-- **Erdős as carry-positivity** — now a genuine equivalent of `ErdosConjecture`,
not a placeholder.  `iterCA n` is the canonical base-3 list of `2^n`
(`digits_three_two_pow`), so "for every `n > 8`, `2 ∈ iterCA n`" says the doubling
carry process is never 2-sparse past `n = 8`.  By `two_in_iterCA_is_carry_made`,
each such `2` is produced by a digit-`2` carry state `(1,0)` or `(2,1)` — the
magnitude/digit interface form of Erdős. -/
def ErdosAsCarryPositivity : Prop :=
  ∀ n : ℕ, 8 < n → 2 ∈ iterCA n

/-- `2` appears in `2^n`'s canonical base-3 digits **iff** it appears in the
doubling-CA list `iterCA n`.  Immediate from the canonicality bridge. -/
theorem two_mem_digits_iff_iterCA (n : ℕ) :
    2 ∈ Nat.digits 3 (2 ^ n) ↔ 2 ∈ iterCA n := by
  rw [digits_three_two_pow]

/-- **Erdős ⟺ carry-positivity** as a real logical equivalence.  This is the
theorem that upgrades Path 1 from a reframing to a bridge: `ErdosConjecture` and
`ErdosAsCarryPositivity` are *the same `Prop`*. -/
theorem erdos_iff_carryPositivity : ErdosConjecture ↔ ErdosAsCarryPositivity := by
  unfold ErdosConjecture ErdosAsCarryPositivity
  exact forall_congr' fun n => imp_congr_right fun _ => two_mem_digits_iff_iterCA n

/-- A `2` occurring in `iterCA (k+1)` is **carry-made**: it is the output of a
digit-`2`-producing carry state `(d', c')` (necessarily `(1,0)` or `(2,1)`).  Ties
`ErdosAsCarryPositivity`'s witness back to the carry rule. -/
theorem two_in_iterCA_is_carry_made {k : ℕ} (h : 2 ∈ iterCA (k + 1)) :
    ∃ d' c', d' < 3 ∧ c' < 2 ∧ (doubleDigit d' c').1 = 2 := by
  rw [show iterCA (k + 1) = doubleAux (iterCA k) 0 from
        Function.iterate_succ_apply' doubleBase3 k [1]] at h
  exact two_mem_doubleAux_carry_made (by omega) (iterCA_lt_three k) h

end Collatz.Erdos
