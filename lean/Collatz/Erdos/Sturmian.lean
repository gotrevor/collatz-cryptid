import Mathlib

/-!
# Path 4: the leading base-3 digit of `2^n` is Sturmian (hence non-automatic)

The LOW base-3 digits of `2^n` are automatic (periodic — `Equidistribution.lean`).
The **leading** digit is the opposite: it is governed by `{n · log₃2}` (the leading
digit is `1` iff `{n log₃2} < log₃2 ≈ 0.631`, else `2`), an irrational rotation
coding.  Such a sequence is **Sturmian**: factor complexity `p(m) = m + 1`,
aperiodic, and therefore **not automatic** (Cobham: an automatic sequence has
complexity `O(m)` but, being eventually periodic on each arithmetic progression,
cannot realize an irrational rotation).  This pins Erdős's home in the
automata/Cobham face, in *non-automatic* territory — explaining why the
automatic/periodic low-digit methods cannot reach it.

**What is proved here**: the leading digit is always `1` or `2` (clean, in ℕ).
**What is script-verified, not yet Lean-proved**: `p(m) = m + 1` for `m ≤ 17` and
density of leading-`1` `= 0.6308 ≈ log₃2` (`~/personal/tools/sandbox/path4_leading_digit.py`).
The Sturmian/non-automatic conclusion needs irrational-rotation + factor-complexity
machinery (no Sturmian library in mathlib); we record it as the established
finding, not a Lean theorem — the honest boundary.
-/

namespace Collatz.Erdos

/-- The most significant base-3 digit of any positive `m` is `1` or `2`:
it is `< 3` (a digit) and `≠ 0` (leading digit of a positive number). -/
theorem digits_getLast_mem_one_or_two (m : ℕ) (hm : m ≠ 0)
    (hne : Nat.digits 3 m ≠ []) :
    (Nat.digits 3 m).getLast hne = 1 ∨ (Nat.digits 3 m).getLast hne = 2 := by
  have hmem := List.getLast_mem hne
  have hlt := Nat.digits_lt_base (by norm_num : (1 : ℕ) < 3) hmem
  have hne0 : (Nat.digits 3 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 3 hm
  omega

/-- The leading base-3 digit of `2^n`. -/
def leadingDigit (n : ℕ) : ℕ :=
  (Nat.digits 3 (2 ^ n)).getLast
    (Nat.digits_ne_nil_iff_ne_zero.mpr (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)))

/-- **Leading digit of `2^n` is `1` or `2`** (the alphabet of the Sturmian word). -/
theorem leadingDigit_mem (n : ℕ) : leadingDigit n = 1 ∨ leadingDigit n = 2 :=
  digits_getLast_mem_one_or_two (2 ^ n) (pow_ne_zero n (by norm_num))
    (Nat.digits_ne_nil_iff_ne_zero.mpr (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)))

/-- The leading-digit word over `1..N` (values in `{1,2}`); its factor complexity
is `m+1` (Sturmian) by `path4_leading_digit.py`. -/
def leadingWord (N : ℕ) : List ℕ := (List.range N).map (fun n => leadingDigit (n + 1))

/-- Concrete checks (hand-verified): `2¹=2₃`, `2³=22₃`, `2⁴=121₃`, `2⁶=2101₃`. -/
example : leadingDigit 1 = 2 := by decide
example : leadingDigit 3 = 2 := by decide
example : leadingDigit 4 = 1 := by decide
example : leadingDigit 6 = 2 := by decide

end Collatz.Erdos
