import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Base-3 doubling as a 1-D cellular automaton

Multiplication by 2 in base 3, viewed as a digit-by-digit (low-to-high)
CA with a `{0,1}`-valued carry.

The local rule on a digit `d ∈ {0,1,2}` with incoming carry `c ∈ {0,1}`:
  output digit  = (2 d + c) mod 3
  outgoing carry = (2 d + c) div 3

We prove the `ofDigits`-level equivalence (independent of digit-list
canonicality):

  ofDigits 3 (doubleAux L c) = 2 · ofDigits 3 L + c

so iterating from `[1]` computes `2^n` viewed as a base-3 polynomial.
-/

namespace Collatz.Erdos

/-- One CA cell: `(digit, carry) ↦ ((2d+c) mod 3, (2d+c) div 3)`. -/
def doubleDigit (d c : ℕ) : ℕ × ℕ :=
  ((2 * d + c) % 3, (2 * d + c) / 3)

/-- Double a base-3 digit list (low-to-high), threading the carry. -/
def doubleAux : List ℕ → ℕ → List ℕ
  | [], 0 => []
  | [], c@(_ + 1) => [c]
  | d :: ds, c =>
    let p := doubleDigit d c
    p.1 :: doubleAux ds p.2

/-- The CA: double a base-3 digit list (carry starts at 0). -/
def doubleBase3 (L : List ℕ) : List ℕ := doubleAux L 0

/-- Iterate the doubling CA `n` times starting from `[1]`.
This computes `2^n` as a base-3 digit list. -/
def iterCA (n : ℕ) : List ℕ := doubleBase3^[n] [1]

/-- Key invariant: doubling at the `ofDigits` level. -/
theorem ofDigits_doubleAux (L : List ℕ) (c : ℕ) :
    Nat.ofDigits (3 : ℕ) (doubleAux L c) = 2 * Nat.ofDigits (3 : ℕ) L + c := by
  induction L generalizing c with
  | nil =>
    match c with
    | 0 => simp [doubleAux, Nat.ofDigits]
    | _ + 1 => simp [doubleAux, Nat.ofDigits]
  | cons d ds ih =>
    have hmod : (2 * d + c) % 3 + 3 * ((2 * d + c) / 3) = 2 * d + c :=
      Nat.mod_add_div _ _
    have hstep : doubleAux (d :: ds) c =
        (doubleDigit d c).1 :: doubleAux ds (doubleDigit d c).2 := rfl
    rw [hstep, Nat.ofDigits, ih (doubleDigit d c).2, Nat.ofDigits]
    simp only [doubleDigit]
    push_cast
    linarith [hmod]

/-- Corollary: the CA on its no-carry form represents multiplication by 2. -/
theorem ofDigits_doubleBase3 (L : List ℕ) :
    Nat.ofDigits (3 : ℕ) (doubleBase3 L) = 2 * Nat.ofDigits (3 : ℕ) L := by
  have := ofDigits_doubleAux L 0
  simpa [doubleBase3] using this

/-- The iterate-from-`[1]` CA computes `2^n` (as a base-3 polynomial). -/
theorem ofDigits_iterCA (n : ℕ) :
    Nat.ofDigits (3 : ℕ) (iterCA n) = 2 ^ n := by
  induction n with
  | zero => simp [iterCA]
  | succ k ih =>
    have hstep : iterCA (k + 1) = doubleBase3 (iterCA k) :=
      Function.iterate_succ_apply' doubleBase3 k [1]
    rw [hstep, ofDigits_doubleBase3, ih, pow_succ]
    ring

/-! ## Canonicality: `iterCA n` is the *canonical* base-3 digit list of `2^n`

`ofDigits_iterCA` only says `iterCA n` represents `2^n` at the `ofDigits` level;
it does not yet say `iterCA n = Nat.digits 3 (2^n)`.  For that we need the two
canonicality conditions of `Nat.digits_ofDigits`: every entry is `< 3`, and the
list has no leading (high-order) zero.  Both are invariants the doubling CA
preserves, so they lift from the seed `[1]` to every `iterCA n`. -/

/-- Carry-out stays in `{0,1}` when the inputs are valid (`d < 3`, `c < 2`):
`2d + c ≤ 5`, so `(2d+c)/3 ≤ 1`.  The doubling CA preserves a `{0,1}` carry. -/
theorem doubleDigit_carry_lt_two {d c : ℕ} (hd : d < 3) (hc : c < 2) :
    (doubleDigit d c).2 < 2 := by
  interval_cases d <;> interval_cases c <;> decide

/-- **Digit validity.** Doubling a valid base-3 list with a `{0,1}` carry yields a
valid base-3 list: every output entry is `< 3`. -/
theorem doubleAux_lt_three :
    ∀ (L : List ℕ) (c : ℕ), c < 2 → (∀ d ∈ L, d < 3) → ∀ x ∈ doubleAux L c, x < 3
  | [], c, hc, _, x, hx => by
      interval_cases c
      · simp only [doubleAux, List.not_mem_nil] at hx
      · simp only [doubleAux, List.mem_singleton] at hx; omega
  | d :: ds, c, hc, hL, x, hx => by
      have hd : d < 3 := hL d (List.mem_cons_self ..)
      rw [show doubleAux (d :: ds) c
            = (doubleDigit d c).1 :: doubleAux ds (doubleDigit d c).2 from rfl] at hx
      rcases List.mem_cons.mp hx with h | h
      · subst h; simp only [doubleDigit]; omega
      · exact doubleAux_lt_three ds (doubleDigit d c).2 (doubleDigit_carry_lt_two hd hc)
          (fun y hy => hL y (List.mem_cons_of_mem d hy)) x h

/-- **No leading zero.** If the input list has no high-order zero (`getLast? ≠ some 0`,
which also covers the empty list), neither does its double.  The high digit of
`2 · m` is nonzero because the high digit of `m` is, threaded through the carry. -/
theorem doubleAux_getLast?_ne :
    ∀ (L : List ℕ) (c : ℕ), c < 2 → (∀ d ∈ L, d < 3) →
      L.getLast? ≠ some 0 → (doubleAux L c).getLast? ≠ some 0
  | [], c, hc, _, _ => by
      interval_cases c <;> decide
  | [d], c, hc, hL, hlast => by
      have hd : d < 3 := hL d (by simp)
      have hd0 : d ≠ 0 := by simpa using hlast
      interval_cases d <;> interval_cases c <;>
        first | exact (hd0 rfl).elim | decide
  | d :: e :: es, c, hc, hL, hlast => by
      have hd : d < 3 := hL d (List.mem_cons_self ..)
      have hc' : (doubleDigit d c).2 < 2 := doubleDigit_carry_lt_two hd hc
      rw [show doubleAux (d :: e :: es) c
            = (doubleDigit d c).1 :: doubleAux (e :: es) (doubleDigit d c).2 from rfl,
          show doubleAux (e :: es) (doubleDigit d c).2
            = (doubleDigit e (doubleDigit d c).2).1
                :: doubleAux es (doubleDigit e (doubleDigit d c).2).2 from rfl,
          List.getLast?_cons_cons,
          show (doubleDigit e (doubleDigit d c).2).1
                :: doubleAux es (doubleDigit e (doubleDigit d c).2).2
            = doubleAux (e :: es) (doubleDigit d c).2 from rfl]
      refine doubleAux_getLast?_ne (e :: es) (doubleDigit d c).2 hc'
        (fun y hy => hL y (List.mem_cons_of_mem d hy)) ?_
      rwa [List.getLast?_cons_cons] at hlast

/-- Every entry of `iterCA n` is a valid base-3 digit (`< 3`). -/
theorem iterCA_lt_three (n : ℕ) : ∀ x ∈ iterCA n, x < 3 := by
  induction n with
  | zero =>
    intro x hx
    simp only [iterCA, Function.iterate_zero, id, List.mem_singleton] at hx
    omega
  | succ k ih =>
    rw [show iterCA (k + 1) = doubleBase3 (iterCA k) from
          Function.iterate_succ_apply' doubleBase3 k [1], doubleBase3]
    exact doubleAux_lt_three (iterCA k) 0 (by omega) ih

/-- `iterCA n` has no leading zero: its high-order digit is nonzero. -/
theorem iterCA_getLast?_ne (n : ℕ) : (iterCA n).getLast? ≠ some 0 := by
  induction n with
  | zero => simp only [iterCA, Function.iterate_zero, id]; decide
  | succ k ih =>
    rw [show iterCA (k + 1) = doubleBase3 (iterCA k) from
          Function.iterate_succ_apply' doubleBase3 k [1], doubleBase3]
    exact doubleAux_getLast?_ne (iterCA k) 0 (by omega) (iterCA_lt_three k) ih

/-- **The bridge.** `iterCA n` *is* the canonical base-3 representation of `2^n`.
Upgrades `ofDigits_iterCA` (representation) to genuine equality with `Nat.digits`,
via `Nat.digits_ofDigits` and the two canonicality invariants above. -/
theorem digits_three_two_pow (n : ℕ) : Nat.digits 3 (2 ^ n) = iterCA n := by
  have hlast : ∀ (h : iterCA n ≠ []), (iterCA n).getLast h ≠ 0 := by
    intro h hcontra
    have hne := iterCA_getLast?_ne n
    rw [List.getLast?_eq_getLast_of_ne_nil h, hcontra] at hne
    exact hne rfl
  calc Nat.digits 3 (2 ^ n)
      = Nat.digits 3 (Nat.ofDigits 3 (iterCA n)) := by rw [ofDigits_iterCA]
    _ = iterCA n := Nat.digits_ofDigits 3 (by norm_num) (iterCA n) (iterCA_lt_three n) hlast

end Collatz.Erdos
