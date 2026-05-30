import Collatz.Erdos.DoublingCA
import Mathlib

/-!
# The carry process as the magnitude ↔ digit *coupling object* (Path 1, deepened)

The swing-for-the-fences interface object.  `DoublingCA.lean` gives the two faces
of one doubling step separately:

* **magnitude face** (`ofDigits_doubleBase3`): `ofDigits 3 (2L) = 2 · ofDigits 3 L`
  — doubling scales the *value* by exactly ×2.
* **digit face**: doubling rewrites the digit *string*.

Here we exhibit the single object that **couples** them: the **carry count**.
The conservation law

  `s(2L) + 2 · C(L) = 2 · s(L)`            (`digitSum_doubleBase3`)

(`s` = base-3 digit sum, `C(L)` = number of carries doubling `L`) says the digit
sum is *almost* conserved under doubling — the only leak is twice the carry count.
Equivalently `C(L)` is the **digit-sum deficit** `(2 s(L) − s(2L))/2`
(`carryCount_eq_digitSum_deficit`): a carry is a magnitude-threshold event
(`2d+c ≥ 3`) that is bookkept *exactly* by a digit-sum drop.  This is Kummer's
carry/digit-sum law specialised to base-3 doubling.

So one number, `C`, lives on the seam: it is simultaneously a count of size-events
and the exact correction term in the digit-sum recurrence.  Iterating from `[1]`
turns this into a per-step recurrence for the digit sum of `2^n`
(`digitSum_iterCA_succ`).

**Honesty boundary.**  This does *not* prove Erdős or Collatz.  It formalises the
coupling, and it also pins a sharp negative: a digit `2` is **not** the same event
as a carry-out — the state `(d,c) = (1,0)` outputs digit `2` with carry-out `0`
(`doubleBase3 [1] = [2]`, yet `C([1]) = 0`).  So "the digit field is rich" (Erdős)
and "many size-events fire" (the carry count) are genuinely different statements;
the conservation law is the exact, provable relation between them, not an identity
of the two faces.
-/

namespace Collatz.Erdos

/-- Number of carries fired while doubling a base-3 list (with incoming carry `c`).
Mirrors `doubleAux`: each cell contributes its `{0,1}`-valued carry-out. -/
def carryCount : List ℕ → ℕ → ℕ
  | [], _ => 0
  | d :: ds, c => (doubleDigit d c).2 + carryCount ds (doubleDigit d c).2

/-- **Carry conservation (Kummer for base-3 doubling).**  Summing the cell
identity `out + 3·(carry-out) = 2d + (carry-in)` along the list telescopes the
carries, leaving `s(out) + 2·C = 2·s(in) + (incoming carry)`. -/
theorem digitSum_doubleAux (L : List ℕ) (c : ℕ) :
    (doubleAux L c).sum + 2 * carryCount L c = 2 * L.sum + c := by
  induction L generalizing c with
  | nil => rcases c with _ | k <;> simp [doubleAux, carryCount]
  | cons d ds ih =>
    have hmod : (doubleDigit d c).1 + 3 * (doubleDigit d c).2 = 2 * d + c := by
      simp only [doubleDigit]; exact Nat.mod_add_div _ _
    have hih := ih (doubleDigit d c).2
    rw [show doubleAux (d :: ds) c
          = (doubleDigit d c).1 :: doubleAux ds (doubleDigit d c).2 from rfl,
        show carryCount (d :: ds) c
          = (doubleDigit d c).2 + carryCount ds (doubleDigit d c).2 from rfl]
    simp only [List.sum_cons]
    omega

/-- Conservation at the no-incoming-carry level (the actual doubling map):
`s(2L) + 2·C(L) = 2·s(L)`. -/
theorem digitSum_doubleBase3 (L : List ℕ) :
    (doubleBase3 L).sum + 2 * carryCount L 0 = 2 * L.sum := by
  simpa [doubleBase3] using digitSum_doubleAux L 0

/-- **The carry count *is* the digit-sum deficit.**  `2·C(L) = 2·s(L) − s(2L)`.
The coupling constant on the magnitude↔digit seam, in closed form. -/
theorem carryCount_eq_digitSum_deficit (L : List ℕ) :
    2 * carryCount L 0 = 2 * L.sum - (doubleBase3 L).sum := by
  have := digitSum_doubleBase3 L; omega

/-- Per-step digit-sum recurrence for `2^n`: doubling `2^n → 2^(n+1)` drops the
base-3 digit sum by exactly twice the carries that step performs.  A magnitude
recurrence (`digit sum`) whose forcing term is the carry count. -/
theorem digitSum_iterCA_succ (n : ℕ) :
    (iterCA (n + 1)).sum + 2 * carryCount (iterCA n) 0 = 2 * (iterCA n).sum := by
  rw [show iterCA (n + 1) = doubleBase3 (iterCA n) from
        Function.iterate_succ_apply' doubleBase3 n [1]]
  exact digitSum_doubleBase3 (iterCA n)

/-! ## Telescoping the chain: a closed digit-sum ↔ magnitude identity for `2^n`

Iterating `digitSum_iterCA_succ` (`s_{j+1} = 2 s_j − 2 C_j`) from the seed `s_0 = 1`
collapses to one equation: the base-3 digit sum of `2^n` equals `2^n` minus twice a
carry-weighted sum.  Stated additively (no ℕ subtraction):

  `s₃(2^n) + 2 · Σ_{j<n} 2^{n-1-j} C_j = 2^n`.

This is the magnitude↔digit bridge in a *single closed identity*: the left summand
is pure digit data, the right side is pure magnitude, and the carry weights are the
coupling.  The geometric weight `2^{n-1-j}` records that an early carry (small `j`)
is doubled many more times, so it costs more magnitude — a carry's "price" is set by
when in the doubling chain it fires. -/

/-- Carries fired by the `j`-th doubling step `2^j → 2^{j+1}`. -/
def stepCarries (j : ℕ) : ℕ := carryCount (iterCA j) 0

/-- Carry-weighted sum `Σ_{j<n} 2^{n-1-j} · C_j`.  Early carries carry more weight
(they survive more doublings). -/
def weightedCarries (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, 2 ^ (n - 1 - j) * stepCarries j

/-- The weight shift on `n → n+1`: every term doubles and a new (unit-weight) term
for step `n` is appended. -/
theorem weightedCarries_succ (n : ℕ) :
    weightedCarries (n + 1) = 2 * weightedCarries n + stepCarries n := by
  unfold weightedCarries
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hlast : (n + 1) - 1 - n = 0 := by omega
  rw [hlast, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hexp : (n + 1) - 1 - j = (n - 1 - j) + 1 := by omega
  rw [hexp, pow_succ]
  ring

/-- **Closed digit-sum / magnitude identity for `2^n`** (CA-list form).
`s(iterCA n) + 2 · weightedCarries n = 2^n`. -/
theorem digitSum_two_pow_closed (n : ℕ) :
    (iterCA n).sum + 2 * weightedCarries n = 2 ^ n := by
  induction n with
  | zero => simp [weightedCarries, iterCA, Function.iterate_zero]
  | succ n ih =>
    rw [weightedCarries_succ]
    have hstep := digitSum_iterCA_succ n
    have hsc : stepCarries n = carryCount (iterCA n) 0 := rfl
    rw [hsc, pow_succ]
    omega

/-- **The headline.**  The base-3 **digit sum of `2^n`**, plus twice a
carry-weighted sum, equals `2^n` itself — a single equation with the digit face on
the left and the magnitude face on the right, coupled by the carry process. -/
theorem digitSum_base3_two_pow (n : ℕ) :
    (Nat.digits 3 (2 ^ n)).sum + 2 * weightedCarries n = 2 ^ n := by
  rw [digits_three_two_pow]
  exact digitSum_two_pow_closed n

/-! ## Avalanche dynamics: how a carry actually *moves* (Path 1, dynamic)

Everything above is kinematic — true for every list, hence not really *about* `2^n`.
The carry has genuine dynamics, though.  Reading low-to-high, an incoming carry
races through a block of `1`s, flipping each to `0`, until it hits a `0`, which
absorbs it and emits a `1`.  This is the odometer avalanche

  `1^k 0  ↦  0^k 1`     (under an incoming carry)

the exact shape of `…0111 + 1 = …1000`, here as the carry sub-process of base-3
doubling.  It is the one mechanism that transports low-digit structure upward into
the high digits — the only bridge across the "low provable / high open" seam. -/

/-- A carry races through a run of `1`s, flipping them to `0` and staying alive. -/
theorem doubleAux_carry_through_ones (k : ℕ) (rest : List ℕ) :
    doubleAux (List.replicate k 1 ++ rest) 1 = List.replicate k 0 ++ doubleAux rest 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append]
    change (0 :: doubleAux (List.replicate k 1 ++ rest) 1)
        = 0 :: (List.replicate k 0 ++ doubleAux rest 1)
    rw [ih]

/-- **The odometer avalanche** `1^k 0 ↦ 0^k 1`: an incoming carry turns a block of
`k` ones followed by a zero into `k` zeros followed by a one, then continues
carry-free.  The complete low-to-high carry propagation event. -/
theorem doubleAux_avalanche (k : ℕ) (rest : List ℕ) :
    doubleAux (List.replicate k 1 ++ 0 :: rest) 1
      = List.replicate k 0 ++ 1 :: doubleAux rest 0 := by
  rw [doubleAux_carry_through_ones]
  congr 1

end Collatz.Erdos
