/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Akiyama's triple-expansion conjecture and Dubickas's `4/3` problem in bases `(q+1)/q`

Work in the rational base `p/q` with `p = q + 1`.  From an integer `x`, the **minimal** digit is the
least `a ∈ {0, …, p-1}` with `q ∣ p * x + a`, namely `a = (-x) mod q`, and it leads to
`(p * x + a) / q = ⌈p x / q⌉`.  The **maximal** digit is the largest such `a`: it is the same digit
unless `x ≡ 0 (mod q)`, where it is `q` instead of `0`.  Iterating gives the minimal and maximal
words of Akiyama-Frougny-Sakarovitch with seed `rep x` (for base `3/2` this identification is proved
against the AFS definition in `Collatz.Antihydra.RationalBase`).

Results:
* `shift`: while the minimal word from `x` avoids `0`, the orbit of `x + 1` is the orbit of `x` plus
  one and its digits are one less.  Hence `avoidsZero_iff`: the minimal word from `x` avoids `0`
  iff the minimal word from `x + 1` avoids `q - 1`.
* `minWord_eq_maxWord_iff`: the minimal and maximal words from `x` coincide iff the minimal word
  avoids `0`.
* `dmStops_ne_zero_iff_ne_one`: Dubickas-Mossinghoff's question (iterate `⌈p x / q⌉` while
  `x mod q ∈ S`; must it stop?) has the same answer for `S = {residues ≠ 0}` and
  `S = {residues ≠ 1}`, and both say "no positive seed has a minimal word that is also maximal".
  By AFS (2008, Section 5) the latter is Akiyama's conjecture that no real has three expansions in
  base `(q+1)/q` (the real-number side is not formalised here).
* `halving` (base `4/3`): the minimal word from `2y` avoids `1` iff the one from `y` avoids `2`.

References: Andrieu-Eliahou-Vivion, arXiv:2510.11723, Question 3.12, Remark 3.14, Prop. 3.10;
Dubickas-Mossinghoff, Math. Comp. 2009; Akiyama-Frougny-Sakarovitch, Israel J. Math. 2008.
-/

namespace Collatz.Antihydra.AkiyamaDubickas

/-- The minimal digit at `x` in base `(q+1)/q`: `(-x) mod q`. -/
def digit (q x : ℕ) : ℕ := (q - x % q) % q

/-- The minimal successor `⌈(q+1) x / q⌉`. -/
def next (q x : ℕ) : ℕ := ((q + 1) * x + digit q x) / q

/-- The maximal digit at `x`: `q` when `q ∣ x`, otherwise the minimal digit. -/
def maxDigit (q x : ℕ) : ℕ := if digit q x = 0 then q else digit q x

/-- The maximal successor. -/
def maxNext (q x : ℕ) : ℕ := ((q + 1) * x + maxDigit q x) / q

/-- The minimal word from seed `x`. -/
def minWord (q x : ℕ) (k : ℕ) : ℕ := digit q ((next q)^[k] x)

/-- The maximal word from seed `x`. -/
def maxWord (q x : ℕ) (k : ℕ) : ℕ := maxDigit q ((maxNext q)^[k] x)

/-! ## Statement-audit checks -/

/-- The minimal digit is admissible and least: it is `< q`, makes `q ∣ (q+1) x + a`, and every
admissible `b ≤ q` with `q ∣ (q+1) x + b` is at least it. -/
theorem digit_spec {q : ℕ} (hq : 0 < q) (x : ℕ) :
    digit q x < q ∧ q ∣ (q + 1) * x + digit q x ∧
      ∀ b ≤ q, q ∣ (q + 1) * x + b → digit q x ≤ b := by
  sorry

/-- The maximal digit is the largest admissible digit `≤ q`. -/
theorem maxDigit_spec {q : ℕ} (hq : 0 < q) (x : ℕ) :
    maxDigit q x ≤ q ∧ q ∣ (q + 1) * x + maxDigit q x ∧
      ∀ b ≤ q, q ∣ (q + 1) * x + b → b ≤ maxDigit q x := by
  sorry

/-- `next` is the ceiling `⌈(q+1) x / q⌉`. -/
theorem next_eq_ceil {q : ℕ} (hq : 0 < q) (x : ℕ) :
    (next q x : ℤ) = ⌈(((q + 1) * x : ℕ) : ℚ) / q⌉ := by
  sorry

/-- Base `4/3` check: the minimal word from `7` starts `2, 2, 1, 2` (`7 → 10 → 14 → 19 → 26`). -/
theorem minWord_three_seven : (List.range 4).map (minWord 3 7) = [2, 2, 1, 2] := by
  decide

/-! ## The shift lemma -/

/-- **Shift.**  If the first `n` minimal digits from `x` are nonzero, then for `k ≤ n` the orbit of
`x + 1` is the orbit of `x` plus one. -/
theorem shift {q : ℕ} (hq : 0 < q) (x n : ℕ) (h : ∀ k < n, minWord q x k ≠ 0) :
    ∀ k ≤ n, (next q)^[k] (x + 1) = (next q)^[k] x + 1 := by
  sorry

/-- The minimal word from `x` avoids `0` iff the minimal word from `x + 1` avoids `q - 1`. -/
theorem avoidsZero_iff {q : ℕ} (hq : 2 ≤ q) (x : ℕ) :
    (∀ k, minWord q x k ≠ 0) ↔ ∀ k, minWord q (x + 1) k ≠ q - 1 := by
  sorry

/-! ## Minimal = maximal exactly when `0` is avoided -/

/-- The minimal and maximal words from `x` coincide iff the minimal word never uses `0`. -/
theorem minWord_eq_maxWord_iff {q : ℕ} (hq : 0 < q) (x : ℕ) :
    minWord q x = maxWord q x ↔ ∀ k, minWord q x k ≠ 0 := by
  sorry

/-! ## Dubickas-Mossinghoff's question -/

/-- Dubickas-Mossinghoff, as stated in AEV Question 3.12 for `p = q + 1`: from every positive
start, iterating `⌈(q+1) x / q⌉` eventually meets a residue outside `S`. -/
def DMStops (q : ℕ) (S : Finset ℕ) : Prop :=
  ∀ x, 0 < x → ∃ k, (next q)^[k] x % q ∉ S

/-- The two cases `S = {residues ≠ 0}` and `S = {residues ≠ 1}` are equivalent, and both say that no
positive seed has a minimal word that is also maximal (Akiyama's conjecture, via AFS §5). -/
theorem dmStops_ne_zero_iff_ne_one {q : ℕ} (hq : 2 ≤ q) :
    (DMStops q ((Finset.range q).erase 0) ↔ DMStops q ((Finset.range q).erase 1)) ∧
      (DMStops q ((Finset.range q).erase 0) ↔ ∀ x, 0 < x → minWord q x ≠ maxWord q x) := by
  sorry

/-! ## Base `4/3`: halving -/

/-- In base `4/3` the minimal word from `2y` avoids `1` iff the minimal word from `y` avoids `2`. -/
theorem halving (y : ℕ) :
    (∀ k, minWord 3 (2 * y) k ≠ 1) ↔ ∀ k, minWord 3 y k ≠ 2 := by
  sorry

end Collatz.Antihydra.AkiyamaDubickas
