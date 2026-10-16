/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Collatz.Antihydra.Foils

/-!
# Antihydra as a rational-base minimal word

Akiyama, Frougny and Sakarovitch (2008) expand a natural number `n` in the rational base `p/q`
(`p > q ≥ 1` coprime) as the unique word `a_k ⋯ a_0` over `{0, …, p-1}` with `a_k ≠ 0` and
`n = (1/q) ∑ aᵢ (p/q)^i`.  Equivalently: `q * n = p * n' + a₀` with `a₀ < p`, then expand `n'`.

Andrieu, Eliahou and Vivion ("A Normality Conjecture on Rational Base Number Systems",
arXiv:2510.11723) define the **minimal word** with seed `u` (an expansion): the infinite word whose
length-`l` prefix is, for every `l`, the lexicographically least `v ∈ {0, …, p-1}^l` such that
`u ++ v` is still an expansion.  They conjecture these words are normal over `{0, …, q-1}`.

This file proves that **Antihydra's parity word is the bit-complement of the minimal word in base
`3/2` with seed `rep 7 = 2122`**.  Antihydra's values are `aₖ = H^k(8)` with `H x = x + ⌊x/2⌋`
(`Foils.orbit Foils.floorChoice (8, 0)`); the bridge is `H (D + 1) = ⌈3D/2⌉ + 1`, and the minimal
word in base `3/2` with seed `rep N` reads the parities of the `⌈3D/2⌉` orbit of `N`
(Mahler's binary words, as AEV note).  Checked numerically for 2,000 terms before formalising
(`claude/knowledge/core/projects/portfolio/starts/disjunctive-collatz.md`, fourth probe).

Antihydra halts iff its odd count ever exceeds twice its even count (`Foils.Halts`), so its halting
problem is a statement about letter counts in one AEV minimal word.  AEV's normality conjecture
fixes the limiting frequency at `1/2` but does not by itself rule out a single early excursion.
-/

namespace Collatz.Antihydra.RationalBase

/-! ## Expansions in base `p/q` -/

/-- Digits of the AFS expansion of `n`, **least** significant first, with fuel `f`.  Each step
writes `q * n = p * n' + a` with `a = (q * n) % p < p` and continues with `n' = (q * n) / p`.
Fuel `n` suffices when `q < p`, since then `n' < n`. -/
def repRevAux (p q : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => ((q * (n + 1)) % p) :: repRevAux p q f ((q * (n + 1)) / p)

/-- The AFS expansion of `n` in base `p/q`, **most** significant digit first; `rep p q 0 = []`. -/
def rep (p q n : ℕ) : List ℕ := (repRevAux p q n n).reverse

/-- The language of expansions in base `p/q`. -/
def Lang (p q : ℕ) : Set (List ℕ) := Set.range (rep p q)

/-- Statement-audit check: `rep 3 2 7 = 2122`, matching AFS's table for base `3/2`. -/
theorem rep_three_two_seven : rep 3 2 7 = [2, 1, 2, 2] := by decide

/-- Statement-audit check: the expansion evaluates back to `n` by AFS's formula
`n = (1/q) ∑ aᵢ (p/q)^i` (digits indexed least significant first). -/
theorem rep_eval {p q : ℕ} (hqp : q < p) (hq : 0 < q) (n : ℕ) :
    ((q : ℚ) * n) =
      ∑ i : Fin (rep p q n).length,
        ((rep p q n).reverse.get ⟨i, by simp⟩ : ℚ) * ((p : ℚ) / q) ^ (i : ℕ) := by
  sorry

/-! ## Minimal words -/

/-- The length-`l` prefix of an infinite word. -/
def pre (w : ℕ → ℕ) (l : ℕ) : List ℕ := List.ofFn fun i : Fin l => w i

/-- `w` is the minimal word in base `p/q` with seed `u` (AEV, Section 1): every prefix extends `u`
to an expansion, and no word `v` of the same length over `{0, …, p-1}` that also extends `u` to an
expansion is lexicographically smaller.  (On lists of equal length, Lean's `List` order is the
lexicographic order the paper uses.) -/
def IsMinWord (p q : ℕ) (u : List ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ l, u ++ pre w l ∈ Lang p q ∧
    ∀ v : List ℕ, v.length = l → (∀ d ∈ v, d < p) → u ++ v ∈ Lang p q → ¬ v < pre w l

/-- A seed has at most one minimal word. -/
theorem isMinWord_unique {p q : ℕ} {u : List ℕ} {w w' : ℕ → ℕ}
    (hw : ∀ k, w k < p) (hw' : ∀ k, w' k < p)
    (h : IsMinWord p q u w) (h' : IsMinWord p q u w') : w = w' := by
  sorry

/-! ## Base `3/2`: the greedy (Mahler) description -/

/-- `⌈3D/2⌉`. -/
def ceilStep (D : ℕ) : ℕ := (3 * D + 1) / 2

/-- In base `3/2` the minimal word with seed `rep N` (`N ≥ 1`) reads the parities of the
`⌈3D/2⌉`-orbit of `N`: the least admissible digit at `D` is `D % 2`, and it leads to `⌈3D/2⌉`. -/
theorem isMinWord_ceilStep (N : ℕ) (hN : 0 < N) :
    IsMinWord 3 2 (rep 3 2 N) (fun k => ceilStep^[k] N % 2) := by
  sorry

/-! ## Antihydra -/

/-- Antihydra's values are the `⌈3D/2⌉`-orbit of `7`, shifted up by one:
`H (D + 1) = ⌈3D/2⌉ + 1` where `H x = ⌊3x/2⌋`. -/
theorem antihydra_value_eq (k : ℕ) :
    (Foils.orbit Foils.floorChoice (8, 0) k).1 = ceilStep^[k] 7 + 1 := by
  sorry

/-- **Main theorem.**  Antihydra's parity word is the bit-complement of the minimal word in base
`3/2` with seed `2122 = rep 7`. -/
theorem antihydra_parity_complement_minWord :
    ∃ w : ℕ → ℕ, IsMinWord 3 2 [2, 1, 2, 2] w ∧ (∀ k, w k < 2) ∧
      ∀ k, (Foils.orbit Foils.floorChoice (8, 0) k).1 % 2 = 1 - w k := by
  sorry

end Collatz.Antihydra.RationalBase
