import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic
import Collatz.Erdos.Basic
import Collatz.Erdos.Conjecture
import Collatz.Erdos.Mahler

/-!
# Axiomatizing abc, Pillai, and Catalan

User directive: **take abc, Pillai, and Catalan/Mihailescu as true** and
use them freely.  This file declares them as `axiom`s and starts deriving
consequences for the Collatz / Erdős / Mahler family.

Status of each, as of 2026:

| name   | proven? | source                            |
|--------|---------|-----------------------------------|
| abc    | open    | Masser–Oesterlé (~1985)           |
| Pillai | open    | (implied by abc)                  |
| Catalan| **theorem** | Mihailescu, 2002              |

Catalan is a genuine theorem, but we don't reprove Mihailescu in Lean —
we cite it as an axiom.  abc and Pillai are still open; we take them on
faith for this exploration.

## Why this is useful

abc and Pillai give bounds on the joint multiplicative behavior of `2`
and `3` that we cannot otherwise prove in elementary Lean.  Combined
with the Lagarias framework from `Erdos/Lagarias.lean`, this lets us
nail down concrete Erdős cases — see `two_pow_eq_two_term_three_pow_sum`
below for the first such derivation.
-/

namespace Collatz.Erdos

/-! ## Axiom 1: abc -/

/-- The **radical** of `n`: product of its distinct prime divisors.
By convention `rad 0 = 1` (empty product); `rad 1 = 1`. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- **abc conjecture** (Masser–Oesterlé, ~1985, open).

For every `ε > 0` there is a constant `K(ε)` such that for every triple
`(a, b, c)` of positive coprime naturals with `a + b = c`,

  `c ≤ K(ε) · rad(a · b · c)^{1+ε}`.

We take this as an axiom. -/
def AbcConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ,
    ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
      ((a + b : ℕ) : ℝ) ≤ K * ((rad (a * b * (a + b)) : ℕ) : ℝ) ^ (1 + ε)

axiom abc : AbcConjecture

/-! ## Axiom 2: Pillai -/

/-- **Pillai's conjecture** (open; implied by abc).  For each fixed `C ≥ 1`,
the equation `a^x = b^y + C` in integers with `a, b, x, y ≥ 2` has only
finitely many solutions. -/
def PillaiConjecture : Prop :=
  ∀ C : ℕ, 1 ≤ C →
    Set.Finite { p : ℕ × ℕ × ℕ × ℕ |
      2 ≤ p.1 ∧ 2 ≤ p.2.1 ∧ 2 ≤ p.2.2.1 ∧ 2 ≤ p.2.2.2 ∧
      p.1 ^ p.2.2.1 = p.2.1 ^ p.2.2.2 + C }

axiom pillai : PillaiConjecture

/-! ## Axiom 3: Catalan-Mihailescu -/

/-- **Catalan–Mihailescu** (Mihailescu, 2002; *theorem*, axiomatized here).
The only solution to `x^p = y^q + 1` with `x, y, p, q ≥ 2` is
`3^2 = 2^3 + 1`. -/
def CatalanMihailescu : Prop :=
  ∀ x y p q : ℕ, 2 ≤ x → 2 ≤ y → 2 ≤ p → 2 ≤ q →
    x ^ p = y ^ q + 1 → x = 3 ∧ y = 2 ∧ p = 2 ∧ q = 3

axiom catalan : CatalanMihailescu

/-! ## First derivation: Erdős for 2-term sums of distinct powers of 3

If `2^n` equals a sum of two distinct powers of 3, then `(n, a, b) = (2, 1, 0)`
— exactly the Erdős exception `2^2 = 4 = 3 + 1 = [1, 1]_3`.

The argument uses Catalan-Mihailescu (axiomatized above) and elementary
divisibility. -/

/-- `3` does not divide `2^n` for any `n`. -/
private theorem three_not_dvd_two_pow (n : ℕ) : ¬ (3 : ℕ) ∣ 2 ^ n := by
  intro hd
  have hcop : Nat.Coprime 3 (2 ^ n) :=
    Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2)
  have h3_one : (3 : ℕ) ∣ 1 := by
    have hgcd := Nat.dvd_gcd (dvd_refl 3) hd
    rw [hcop] at hgcd
    exact hgcd
  exact absurd h3_one (by decide)

/-- **Erdős for 2-term sums** (uses Catalan).

If `2^n = 3^a + 3^b` with `b < a`, then `(n, a, b) = (2, 1, 0)`.  This
identifies the known Erdős exception `N = 2` as the *unique* `n` whose
power of `2` is a sum of exactly two distinct powers of `3`. -/
theorem two_pow_eq_two_term_three_pow_sum {a b n : ℕ} (hab : b < a)
    (h : 2 ^ n = 3 ^ a + 3 ^ b) :
    n = 2 ∧ a = 1 ∧ b = 0 := by
  -- Step 1: b = 0. Otherwise 3 divides the RHS, hence 2^n, contradicting
  -- coprimality.
  have hb_zero : b = 0 := by
    rcases Nat.eq_zero_or_pos b with h0 | hpos
    · exact h0
    · exfalso
      apply three_not_dvd_two_pow n
      rw [h]
      have ha_ne : a ≠ 0 := by omega
      exact dvd_add (dvd_pow_self 3 ha_ne) (dvd_pow_self 3 hpos.ne')
  subst hb_zero
  rw [pow_zero] at h
  -- h : 2^n = 3^a + 1, with a ≥ 1.
  have ha_pos : 1 ≤ a := hab
  -- Case on a.
  rcases Nat.lt_or_ge a 2 with ha_lt | ha_ge
  · -- a = 1 (since a ≥ 1).
    interval_cases a
    -- a = 1: 2^n = 4, so n = 2.
    have h4 : 2 ^ n = 2 ^ 2 := by simp; omega
    have hn : n = 2 := Nat.pow_right_injective (le_refl 2) h4
    exact ⟨hn, rfl, rfl⟩
  · -- a ≥ 2. Case on n.
    rcases Nat.lt_or_ge n 2 with hn_lt | hn_ge
    · -- n < 2.
      interval_cases n
      · -- n = 0: 1 = 3^a + 1, impossible since 3^a ≥ 1.
        have h_pos : 0 < (3 : ℕ) ^ a := pow_pos (by decide : (0:ℕ) < 3) a
        simp at h
      · -- n = 1: 2 = 3^a + 1, so 3^a = 1, so a = 0, contradicting a ≥ 2.
        have h3a : (3 : ℕ) ^ a = 1 := by linarith
        have ha0 : a = 0 := (Nat.pow_eq_one.mp h3a).resolve_left (by decide)
        omega
    · -- n ≥ 2 and a ≥ 2. Apply Catalan to x = 2, y = 3, p = n, q = a.
      have hcat := catalan 2 3 n a (by decide) (by decide) hn_ge ha_ge h
      exact absurd hcat.1 (by decide)

/-- Sanity check: the conclusion of `two_pow_eq_two_term_three_pow_sum`
matches the Erdős exception `2^2 = 4`. -/
example : (2 : ℕ) ^ 2 = 3 ^ 1 + 3 ^ 0 := by decide

/-! ## Axiom 4: Furstenberg-style ×2,×3 digit stiffness

The digit-level shadow of Furstenberg's ×2,×3 rigidity.  See
`Erdos/Equidistribution.lean` for the *provable* half (low base-3 digits of
`2^n` equidistribute, because `2` is a primitive root mod `3^k`); this axiom
supplies the *open* half (the full digit string is pseudorandom). -/

/-- **Furstenberg-style ×2,×3 digit stiffness** (open).

Because `2` and `3` are multiplicatively independent, the base-3 digit string of
`2^n` is conjecturally pseudorandom (a consequence of Furstenberg's ×2,×3
rigidity / the normality it underwrites): **every** digit value `v ∈ {0,1,2}`
occurs in `2^n` for all sufficiently large `n`.

This is *stronger* than Erdős (which is just the case `v = 2`).  We axiomatize
the digit-randomness picture to trace what it buys.

⚠️ **Honesty note**: this does NOT reduce the open content — it *names* it.
Deriving Erdős from it is "assume the deep pseudorandomness, recover the specific
instance," not external leverage.  The genuinely deep parent is the
topological/measure ×2,×3 rigidity; this is its digit-level form, stated at the
altitude that plugs into Erdős.  Per `Partial.erdos_odd`, the odd-`n` case is
already unconditional (low digit), so the axiom's real job is the **even** tail. -/
def FurstenbergDigitStiffness : Prop :=
  ∀ v : ℕ, v < 3 → ∃ N : ℕ, ∀ n : ℕ, N < n → v ∈ Nat.digits 3 (2 ^ n)

axiom furstenbergStiffness : FurstenbergDigitStiffness

/-- **Eventual Erdős**: `2` appears in `2^n` for all large `n`. -/
def EventualErdos : Prop := ∃ N : ℕ, ∀ n : ℕ, N < n → 2 ∈ Nat.digits 3 (2 ^ n)

/-- Stiffness ⟹ eventual Erdős (specialize the stiffness to the digit `v = 2`). -/
theorem eventualErdos_of_stiffness (h : FurstenbergDigitStiffness) : EventualErdos :=
  h 2 (by decide)

/-- Modulo the axiom, eventual Erdős holds outright. -/
theorem eventualErdos : EventualErdos := eventualErdos_of_stiffness furstenbergStiffness

/-- **Full Erdős = finite window + infinite tail** (a split of ℕ at `N`, NOT a
reduction to computation).  Given the tail (`2 ∈ digits 3 (2^n)` for `n > N`) and
the finite window `8 < n ≤ N`, full `ErdosConjecture` follows.

⚠️ This does **not** reduce Erdős to a finite computation.  Only the *window* is
finite; the *tail* is infinite and *is* the conjecture.  The Furstenberg axiom
supplies the tail only by **assuming** an open conjecture, and even then
**ineffectively**: `FurstenbergDigitStiffness` gives `∃ N` with no computable
value, so one cannot extract a concrete `N` to run the window up to.  Indeed the
bare axiom proves only `eventualErdos` (the `n > N` form), **not** the `n > 8`
form — the missing piece is exactly an *effective* exception bound, which is
unknown.  Same finiteness-without-effectivity wall as abc for the S-unit family. -/
theorem erdos_of_tail_and_window {N : ℕ}
    (htail : ∀ n, N < n → 2 ∈ Nat.digits 3 (2 ^ n))
    (hwindow : ∀ n, 8 < n → n ≤ N → 2 ∈ Nat.digits 3 (2 ^ n)) :
    ErdosConjecture := by
  intro n hn
  by_cases h1 : n ≤ N
  · exact hwindow n hn h1
  · exact htail n (not_le.mp h1)

end Collatz.Erdos
