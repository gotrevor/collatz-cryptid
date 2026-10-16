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
`(p * x + a) / q = ⌈p x / q⌉`.  The **maximal** digit is the largest such `a`: it is the
same digit unless `x ≡ 0 (mod q)`, where it is `q` instead of `0`.  Iterating gives the
minimal and maximal words of Akiyama-Frougny-Sakarovitch with seed `rep x` (for base
`3/2` this identification is proved against the AFS definition in
`Collatz.Antihydra.RationalBase`).

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
  have hx : x % q < q := Nat.mod_lt x hq
  have hdigit : digit q x = if x % q = 0 then 0 else q - x % q := by
    by_cases hr : x % q = 0
    · simp [digit, hr]
    · have : q - x % q < q := by omega
      simp [digit, hr, Nat.mod_eq_of_lt this]
  have hdiv (b : ℕ) : q ∣ (q + 1) * x + b ↔ q ∣ x + b := by
    have heq : (q + 1) * x + b = q * x + (x + b) := by ring
    rw [heq]
    simpa [add_comm] using
      (Nat.dvd_add_iff_left (dvd_mul_right q x) : q ∣ x + b ↔ q ∣ x + b + q * x).symm
  constructor
  · rw [hdigit]
    split <;> omega
  constructor
  · rw [hdiv, hdigit]
    by_cases hr : x % q = 0
    · simpa [hr] using Nat.dvd_of_mod_eq_zero hr
    · simp only [if_neg hr]
      have hdecomp := Nat.div_add_mod x q
      have heq : x + (q - x % q) = q * (x / q + 1) := by
        rw [Nat.mul_add]
        omega
      rw [heq]
      exact dvd_mul_right q (x / q + 1)
  · intro b hb hdvd
    rw [hdiv, Nat.dvd_iff_mod_eq_zero, Nat.add_mod] at hdvd
    by_cases hbq : b = q
    · rw [hdigit]
      split <;> omega
    have hblt : b < q := by omega
    rw [Nat.mod_eq_of_lt hblt] at hdvd
    rw [hdigit]
    by_cases hr : x % q = 0
    · simp [hr]
    · simp only [if_neg hr]
      by_contra hnot
      have hsumlt : x % q + b < q := by omega
      rw [Nat.mod_eq_of_lt hsumlt] at hdvd
      omega

/-- The maximal digit is the largest admissible digit `≤ q`. -/
theorem maxDigit_spec {q : ℕ} (hq : 0 < q) (x : ℕ) :
    maxDigit q x ≤ q ∧ q ∣ (q + 1) * x + maxDigit q x ∧
      ∀ b ≤ q, q ∣ (q + 1) * x + b → b ≤ maxDigit q x := by
  have hs := digit_spec hq x
  by_cases hz : digit q x = 0
  · simp only [maxDigit, if_pos hz]
    constructor
    · exact le_rfl
    constructor
    · have hd : q ∣ (q + 1) * x := by simpa [hz] using hs.2.1
      exact dvd_add hd (dvd_refl q)
    · exact fun b hb _ ↦ hb
  · simp only [maxDigit, if_neg hz]
    constructor
    · exact hs.1.le
    constructor
    · exact hs.2.1
    · intro b hb hadm
      have hdb : digit q x ≤ b := hs.2.2 b hb hadm
      by_contra hnot
      have hlt : digit q x < b := by omega
      have heq : (q + 1) * x + b =
          (b - digit q x) + ((q + 1) * x + digit q x) := by omega
      have hdiff : q ∣ b - digit q x :=
        (Nat.dvd_add_iff_left hs.2.1).mpr (heq ▸ hadm)
      have hqle : q ≤ b - digit q x := Nat.le_of_dvd (by omega) hdiff
      omega

/-- `next` is the ceiling `⌈(q+1) x / q⌉`. -/
theorem next_eq_ceil {q : ℕ} (hq : 0 < q) (x : ℕ) :
    (next q x : ℤ) = ⌈(((q + 1) * x : ℕ) : ℚ) / q⌉ := by
  have hs := digit_spec hq x
  have hmul : q * next q x = (q + 1) * x + digit q x := by
    exact Nat.mul_div_cancel' hs.2.1
  have hmulQ : (q : ℚ) * next q x = (q + 1) * x + digit q x := by
    exact_mod_cast hmul
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hdQ : (digit q x : ℚ) < q := by exact_mod_cast hs.1
  symm
  rw [Int.ceil_eq_iff]
  norm_num only [Int.cast_natCast, Int.cast_one]
  push_cast at hmulQ ⊢
  constructor
  · rw [lt_div_iff₀ hqQ]
    nlinarith
  · rw [div_le_iff₀ hqQ]
    nlinarith

/-- Base `4/3` check: the minimal word from `7` starts `2, 2, 1, 2`
(`7 → 10 → 14 → 19 → 26`). -/
theorem minWord_three_seven : (List.range 4).map (minWord 3 7) = [2, 2, 1, 2] := by
  decide

/-! ## The shift lemma -/

private lemma digit_succ_of_ne_zero {q y : ℕ} (hq : 0 < q) (hy : digit q y ≠ 0) :
    digit q (y + 1) = digit q y - 1 := by
  have hySpec := digit_spec hq y
  have hsSpec := digit_spec hq (y + 1)
  have heq : (q + 1) * (y + 1) + (digit q y - 1) =
      ((q + 1) * y + digit q y) + q := by
    ring_nf
    omega
  have hdvd : q ∣ (q + 1) * (y + 1) + (digit q y - 1) := by
    rw [heq]
    exact dvd_add hySpec.2.1 (dvd_refl q)
  have hle : digit q (y + 1) ≤ digit q y - 1 :=
    hsSpec.2.2 _ (by omega) hdvd
  have heq' : (q + 1) * (y + 1) + digit q (y + 1) =
      ((q + 1) * y + (digit q (y + 1) + 1)) + q := by ring
  have hdvd' : q ∣ (q + 1) * y + (digit q (y + 1) + 1) :=
    (Nat.dvd_add_iff_left (dvd_refl q)).mpr (heq' ▸ hsSpec.2.1)
  have hge : digit q y ≤ digit q (y + 1) + 1 :=
    hySpec.2.2 _ (by omega) hdvd'
  omega

private lemma next_succ_of_digit_ne_zero {q y : ℕ} (hq : 0 < q) (hy : digit q y ≠ 0) :
    next q (y + 1) = next q y + 1 := by
  rw [next, next, digit_succ_of_ne_zero hq hy]
  have heq : (q + 1) * (y + 1) + (digit q y - 1) =
      ((q + 1) * y + digit q y) + q := by
    ring_nf
    omega
  rw [heq, Nat.add_div_right _ hq]

private lemma digit_succ_of_eq_zero {q y : ℕ} (hq : 2 ≤ q) (hy : digit q y = 0) :
    digit q (y + 1) = q - 1 := by
  have hs := digit_spec (q := q) (by omega) y
  have hd : q ∣ (q + 1) * y := by simpa [hy] using hs.2.1
  have heq : (q + 1) * y = q * y + y := by ring
  rw [heq] at hd
  have hyDvd : q ∣ y := (Nat.dvd_add_iff_right (dvd_mul_right q y)).mpr hd
  have hyMod : y % q = 0 := Nat.dvd_iff_mod_eq_zero.mp hyDvd
  have hsuccMod : (y + 1) % q = 1 := by
    simpa [hyMod, Nat.mod_eq_of_lt (by omega : 1 < q)] using Nat.add_mod y 1 q
  rw [digit, hsuccMod, Nat.mod_eq_of_lt (by omega)]

/-- **Shift.**  If the first `n` minimal digits from `x` are nonzero, then for `k ≤ n` the
orbit of `x + 1` is the orbit of `x` plus one. -/
theorem shift {q : ℕ} (hq : 0 < q) (x n : ℕ) (h : ∀ k < n, minWord q x k ≠ 0) :
    ∀ k ≤ n, (next q)^[k] (x + 1) = (next q)^[k] x + 1 := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      exact next_succ_of_digit_ne_zero hq (h k (by omega))

/-- The minimal word from `x` avoids `0` iff the minimal word from `x + 1` avoids `q - 1`. -/
theorem avoidsZero_iff {q : ℕ} (hq : 2 ≤ q) (x : ℕ) :
    (∀ k, minWord q x k ≠ 0) ↔ ∀ k, minWord q (x + 1) k ≠ q - 1 := by
  have hqpos : 0 < q := by omega
  constructor
  · intro hzero k hbad
    have hshift := shift hqpos x k (fun j _ ↦ hzero j) k le_rfl
    have hyne : digit q ((next q)^[k] x) ≠ 0 := hzero k
    have hdlt := (digit_spec hqpos ((next q)^[k] x)).1
    unfold minWord at hbad
    rw [hshift, digit_succ_of_ne_zero hqpos hyne] at hbad
    omega
  · intro hmax k hk
    have hex : ∃ j, minWord q x j = 0 := ⟨k, by simpa using hk⟩
    let j := Nat.find hex
    have hjzero : minWord q x j = 0 := Nat.find_spec hex
    have hjprev : ∀ i < j, minWord q x i ≠ 0 := by
      intro i hi hizero
      exact (Nat.not_lt_of_ge (Nat.find_min' hex hizero)) hi
    have hshift := shift hqpos x j hjprev j le_rfl
    apply hmax j
    unfold minWord at hjzero ⊢
    rw [hshift, digit_succ_of_eq_zero hq hjzero]

/-! ## Minimal = maximal exactly when `0` is avoided -/

private lemma maxDigit_ne_zero {q y : ℕ} (hq : 0 < q) : maxDigit q y ≠ 0 := by
  by_cases hy : digit q y = 0
  · simp [maxDigit, hy, hq.ne']
  · simp [maxDigit, hy]

private lemma maxNext_eq_next {q y : ℕ} (hy : digit q y ≠ 0) :
    maxNext q y = next q y := by
  simp [maxNext, next, maxDigit, hy]

/-- The minimal and maximal words from `x` coincide iff the minimal word never uses `0`. -/
theorem minWord_eq_maxWord_iff {q : ℕ} (hq : 0 < q) (x : ℕ) :
    minWord q x = maxWord q x ↔ ∀ k, minWord q x k ≠ 0 := by
  constructor
  · intro heq k
    rw [heq]
    unfold maxWord
    exact maxDigit_ne_zero hq
  · intro hzero
    have horbit : ∀ k, (maxNext q)^[k] x = (next q)^[k] x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          exact maxNext_eq_next (hzero k)
    funext k
    have hd : digit q ((next q)^[k] x) ≠ 0 := hzero k
    rw [minWord, maxWord, horbit k, maxDigit, if_neg hd]

/-! ## Dubickas-Mossinghoff's question -/

/-- Dubickas-Mossinghoff, as stated in AEV Question 3.12 for `p = q + 1`: from every positive
start, iterating `⌈(q+1) x / q⌉` eventually meets a residue outside `S`. -/
def DMStops (q : ℕ) (S : Finset ℕ) : Prop :=
  ∀ x, 0 < x → ∃ k, (next q)^[k] x % q ∉ S

private lemma digit_eq_zero_iff {q y : ℕ} (hq : 0 < q) : digit q y = 0 ↔ y % q = 0 := by
  have hr : y % q < q := Nat.mod_lt y hq
  by_cases hy : y % q = 0
  · simp [digit, hy]
  · have hsub : q - y % q < q := by omega
    rw [digit, Nat.mod_eq_of_lt hsub]
    omega

private lemma digit_eq_top_iff {q y : ℕ} (hq : 2 ≤ q) :
    digit q y = q - 1 ↔ y % q = 1 := by
  have hr : y % q < q := Nat.mod_lt y (by omega)
  by_cases hy : y % q = 0
  · simp [digit, hy]
    omega
  · have hsub : q - y % q < q := by omega
    rw [digit, Nat.mod_eq_of_lt hsub]
    omega

/-- The two cases `S = {residues ≠ 0}` and `S = {residues ≠ 1}` are equivalent, and both
say that no positive seed has a minimal word that is also maximal (Akiyama's conjecture,
via AFS §5). -/
theorem dmStops_ne_zero_iff_ne_one {q : ℕ} (hq : 2 ≤ q) :
    (DMStops q ((Finset.range q).erase 0) ↔ DMStops q ((Finset.range q).erase 1)) ∧
      (DMStops q ((Finset.range q).erase 0) ↔ ∀ x, 0 < x → minWord q x ≠ maxWord q x) := by
  have hqpos : 0 < q := by omega
  have hzero : DMStops q ((Finset.range q).erase 0) ↔
      ∀ x, 0 < x → ∃ k, minWord q x k = 0 := by
    constructor
    · intro h x hx
      obtain ⟨k, hk⟩ := h x hx
      refine ⟨k, (digit_eq_zero_iff hqpos).2 ?_⟩
      simpa [Finset.mem_erase, Nat.mod_lt _ hqpos] using hk
    · intro h x hx
      obtain ⟨k, hk⟩ := h x hx
      refine ⟨k, ?_⟩
      have hmod := (digit_eq_zero_iff hqpos).1 hk
      simpa [Finset.mem_erase, Nat.mod_lt _ hqpos] using hmod
  have hone : DMStops q ((Finset.range q).erase 1) ↔
      ∀ x, 0 < x → ∃ k, minWord q x k = q - 1 := by
    constructor
    · intro h x hx
      obtain ⟨k, hk⟩ := h x hx
      refine ⟨k, (digit_eq_top_iff hq).2 ?_⟩
      simpa [Finset.mem_erase, Nat.mod_lt _ hqpos] using hk
    · intro h x hx
      obtain ⟨k, hk⟩ := h x hx
      refine ⟨k, ?_⟩
      have hmod := (digit_eq_top_iff hq).1 hk
      simpa [Finset.mem_erase, Nat.mod_lt _ hqpos] using hmod
  constructor
  · rw [hzero, hone]
    constructor
    · intro h x hx
      cases x with
      | zero => omega
      | succ x =>
          cases x with
          | zero =>
              refine ⟨0, (digit_eq_top_iff hq).2 ?_⟩
              simp [Nat.mod_eq_of_lt (by omega : 1 < q)]
          | succ x =>
              have hex := h (x + 1) (by omega)
              have hnot : ¬∀ k, minWord q (x + 1) k ≠ 0 := by
                push Not
                exact hex
              rw [avoidsZero_iff hq] at hnot
              push Not at hnot
              simpa [Nat.add_assoc] using hnot
    · intro h x hx
      have hex := h (x + 1) (by omega)
      have hnot : ¬∀ k, minWord q (x + 1) k ≠ q - 1 := by
        push Not
        exact hex
      rw [← avoidsZero_iff hq] at hnot
      push Not at hnot
      exact hnot
  · rw [hzero]
    constructor
    · intro h x hx heq
      obtain ⟨k, hk⟩ := h x hx
      have hall := (minWord_eq_maxWord_iff hqpos x).1 heq
      exact hall k hk
    · intro h x hx
      by_contra hnot
      push Not at hnot
      have hall : ∀ k, minWord q x k ≠ 0 := by
        intro k hk
        exact hnot k hk
      exact h x hx ((minWord_eq_maxWord_iff hqpos x).2 hall)

/-! ## Base `4/3`: halving -/

private lemma digit_double_eq_one_iff (y : ℕ) : digit 3 (2 * y) = 1 ↔ digit 3 y = 2 := by
  unfold digit
  omega

private lemma next_double_of_digit_ne_one (y : ℕ) (h : digit 3 (2 * y) ≠ 1) :
    next 3 (2 * y) = 2 * next 3 y := by
  unfold next digit at *
  omega

/-- In base `4/3` the minimal word from `2y` avoids `1` iff the minimal word from `y` avoids `2`. -/
theorem halving (y : ℕ) :
    (∀ k, minWord 3 (2 * y) k ≠ 1) ↔ ∀ k, minWord 3 y k ≠ 2 := by
  constructor
  · intro hleft
    have horbit : ∀ k, (next 3)^[k] (2 * y) = 2 * (next 3)^[k] y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          apply next_double_of_digit_ne_one
          intro hk
          apply hleft k
          simpa [minWord, ih]
    intro k hk
    apply hleft k
    unfold minWord
    rw [horbit k]
    exact (digit_double_eq_one_iff _).2 hk
  · intro hright
    have horbit : ∀ k, (next 3)^[k] (2 * y) = 2 * (next 3)^[k] y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          apply next_double_of_digit_ne_one
          intro hk
          exact hright k ((digit_double_eq_one_iff _).1 hk)
    intro k hk
    apply hright k
    apply (digit_double_eq_one_iff _).1
    unfold minWord at hk
    rw [horbit k] at hk
    exact hk

/-! ## General shift and scaling

The two moves behind every reduction above.  Shifting by `c` lowers each digit by `c` while
all digits stay `≥ c`; scaling by `m` multiplies each digit by `m` while the products stay
`< q`.  When `m ∣ q + 1`, a digit divisible by `m` forces the successor to be divisible by
`m`, which is what lets base `4/3` absorb odd starts.
-/

/-- **Shift by `c`.**  While the minimal digits from `x` are all `≥ c`, the orbit of `x + c` is
the orbit of `x` plus `c`. -/
theorem shift_add {q : ℕ} (hq : 0 < q) (c x n : ℕ) (h : ∀ k < n, c ≤ minWord q x k) :
    ∀ k ≤ n, (next q)^[k] (x + c) = (next q)^[k] x + c := by
  sorry

/-- The digits of the shifted word are the original digits minus `c`. -/
theorem minWord_shift_add {q : ℕ} (hq : 0 < q) (c x n : ℕ) (h : ∀ k < n, c ≤ minWord q x k) :
    ∀ k < n, minWord q (x + c) k = minWord q x k - c := by
  sorry

/-- **Scale by `m`.**  While `m` times each minimal digit from `y` stays below `q`, the orbit of
`m * y` is `m` times the orbit of `y`. -/
theorem scale {q : ℕ} (m y n : ℕ) (h : ∀ k < n, m * minWord q y k < q) :
    ∀ k ≤ n, (next q)^[k] (m * y) = m * (next q)^[k] y := by
  sorry

/-- The digits of the scaled word are `m` times the original digits. -/
theorem minWord_scale {q : ℕ} (m y n : ℕ) (h : ∀ k < n, m * minWord q y k < q) :
    ∀ k < n, minWord q (m * y) k = m * minWord q y k := by
  sorry

/-- If `m ∣ q + 1` and `m` divides the minimal digit at `x`, then `m` divides the successor:
`q * next q x = (q + 1) * x + digit q x` and `m` is coprime to `q`. -/
theorem dvd_next_of_dvd_digit {q m : ℕ} (hq : 0 < q) (hm : m ∣ q + 1) (x : ℕ)
    (h : m ∣ digit q x) : m ∣ next q x := by
  sorry

/-! ## Base `4/3`: every case of the Dubickas-Mossinghoff problem

Residues and digits in base `4/3`: residue `0` is digit `0`, residue `1` is digit `2`, and
residue `2` is digit `1`.  `dmStops_ne_zero_iff_ne_one` covers `S = {1, 2}` and `S = {0, 2}`
(the latter is Dubickas-Mossinghoff's "4/3 problem").  The remaining pair `S = {0, 1}` (avoid
digit `1`) reduces to `S = {0, 2}` by one step and `halving`: a digit other than `1` makes the
successor even.  So every nontrivial case is Akiyama's conjecture in base `4/3`.
-/

/-- **Singletons stop** (Dubickas-Mossinghoff, Prop. 3.2, in base `(q+1)/q`): a positive orbit
cannot keep one residue forever, since then `q ^ k ∣ x + a` for every `k`. -/
theorem dmStops_singleton {q : ℕ} (hq : 2 ≤ q) (r : ℕ) : DMStops q {r} := by
  sorry

/-- The empty set stops at once. -/
theorem dmStops_empty (q : ℕ) : DMStops q ∅ := by
  sorry

/-- The full residue set never stops. -/
theorem not_dmStops_range {q : ℕ} (hq : 0 < q) : ¬ DMStops q (Finset.range q) := by
  sorry

/-- Base `4/3`: avoiding residue `2` (digit `1`) is the same problem as avoiding residue `1`
(digit `2`). -/
theorem dmStops_ne_two_iff_ne_one :
    DMStops 3 ((Finset.range 3).erase 2) ↔ DMStops 3 ((Finset.range 3).erase 1) := by
  sorry

/-- **The whole `4/3` problem is Akiyama's conjecture.**  Every two-residue case of
Dubickas-Mossinghoff's question in base `4/3` holds iff no positive seed has a minimal word
that is also maximal. -/
theorem dm43_pair_iff (S : Finset ℕ) (hS : S ⊆ Finset.range 3) (hcard : S.card = 2) :
    DMStops 3 S ↔ ∀ x, 0 < x → minWord 3 x ≠ maxWord 3 x := by
  sorry

/-- The classification by size: at most one residue always stops, two residues is Akiyama's
conjecture, and all three never stop. -/
theorem dm43_classification (S : Finset ℕ) (hS : S ⊆ Finset.range 3) :
    (S.card ≤ 1 → DMStops 3 S) ∧
      (S.card = 2 → (DMStops 3 S ↔ ∀ x, 0 < x → minWord 3 x ≠ maxWord 3 x)) ∧
      (S.card = 3 → ¬ DMStops 3 S) := by
  sorry

end Collatz.Antihydra.AkiyamaDubickas
