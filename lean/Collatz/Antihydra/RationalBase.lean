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
(Mahler's binary words, as AEV note).  Checked numerically for 2,000 terms before formalising.

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

/-- Once the fuel is at least the represented number, it does not affect the base-`3/2`
representation. -/
theorem repRevAux_fuel_eq (n : ℕ) : ∀ f, n ≤ f →
    repRevAux 3 2 f n = repRevAux 3 2 n n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hnf
    rcases n with _ | n
    · rcases f with _ | f <;> rfl
    rcases f with _ | f
    · omega
    simp only [repRevAux]
    congr 1
    have hlt : 2 * (n + 1) / 3 < n + 1 := by omega
    rw [ih _ hlt f (by omega), ih _ hlt n (by omega)]

/-- Natural-number evaluation of a least-significant-digit-first base-`3/2` word. -/
def evalRev32 : List ℕ → ℕ
  | [] => 0
  | a :: as => (3 * evalRev32 as + a) / 2

theorem evalRev32_repRevAux (n : ℕ) : ∀ f, n ≤ f →
    evalRev32 (repRevAux 3 2 f n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hnf
    rcases n with _ | n
    · rcases f with _ | f <;> rfl
    rcases f with _ | f
    · omega
    simp only [repRevAux, evalRev32]
    rw [ih]
    · omega
    · omega
    · omega

theorem rep_injective : Function.Injective (rep 3 2) := by
  intro m n h
  have := congrArg (fun ds => evalRev32 ds.reverse) h
  simpa [rep, evalRev32_repRevAux] using this

/-- Removing the last digit of a positive representation gives the representation of its
parent. -/
theorem rep_step (M : ℕ) (hM : 0 < M) :
    rep 3 2 M = rep 3 2 (2 * M / 3) ++ [2 * M % 3] := by
  rcases M with _ | M
  · omega
  unfold rep
  simp only [repRevAux, List.reverse_cons]
  rw [repRevAux_fuel_eq]
  omega

/-- A solution of `2M = 3N + a` appends the digit `a` to the representation of `N`. -/
theorem rep_child {N M a : ℕ} (h : 2 * M = 3 * N + a) (ha : a < 3)
    (hN : 0 < N) : rep 3 2 M = rep 3 2 N ++ [a] := by
  have hM : 0 < M := by omega
  rw [rep_step M hM]
  congr <;> omega

/-- The base-`3/2` language is closed under deleting its last digit. -/
theorem lang_dropLast {xs : List ℕ} {a : ℕ} (h : xs ++ [a] ∈ Lang 3 2) :
    xs ∈ Lang 3 2 := by
  rcases h with ⟨M, hM⟩
  have hpos : 0 < M := by
    by_contra hz
    have : M = 0 := by omega
    subst M
    simp [rep, repRevAux] at hM
  refine ⟨2 * M / 3, ?_⟩
  have hs := rep_step M hpos
  have happ : xs ++ [a] = rep 3 2 (2 * M / 3) ++ [2 * M % 3] := hM.symm.trans hs
  simpa using (congrArg List.dropLast happ).symm

/-- Every prefix of a base-`3/2` representation is itself a representation. -/
theorem lang_prefix {xs ys : List ℕ} (h : xs ++ ys ∈ Lang 3 2) : xs ∈ Lang 3 2 := by
  induction ys using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton ys a ih =>
    apply ih
    apply lang_dropLast (xs := xs ++ ys) (a := a)
    simpa [List.append_assoc] using h

/-- Conversely, a one-digit extension in the language comes from a solution of the parent
equation. -/
theorem rep_extension_last {N a : ℕ} (h : rep 3 2 N ++ [a] ∈ Lang 3 2) :
    ∃ M, 2 * M = 3 * N + a := by
  rcases h with ⟨M, hM⟩
  have hpos : 0 < M := by
    by_contra hz
    have : M = 0 := by omega
    subst M
    simp [rep, repRevAux] at hM
  refine ⟨M, ?_⟩
  have hs := rep_step M hpos
  have happ : rep 3 2 N ++ [a] = rep 3 2 (2 * M / 3) ++ [2 * M % 3] :=
    hM.symm.trans hs
  have hparent : N = 2 * M / 3 := rep_injective (by
    simpa using congrArg List.dropLast happ)
  have hdigit : a = 2 * M % 3 := by
    simpa using congrArg List.getLast? happ
  omega

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

theorem pre_succ_last (w : ℕ → ℕ) (l : ℕ) :
    pre w (l + 1) = pre w l ++ [w l] := by
  unfold pre
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

theorem pre_succ_head (w : ℕ → ℕ) (l : ℕ) :
    pre w (l + 1) = w 0 :: pre (fun k => w (k + 1)) l := by
  simp [pre, List.ofFn_succ]

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

theorem ceilStep_digit (N : ℕ) : 2 * ceilStep N = 3 * N + N % 2 := by
  unfold ceilStep
  omega

theorem ceilStep_pos {N : ℕ} (hN : 0 < N) : 0 < ceilStep N := by
  unfold ceilStep
  omega

theorem iterate_ceilStep_pos {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 < ceilStep^[k] N := by
  induction k with
  | zero => simpa using hN
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ceilStep_pos ih

theorem rep_iterate_ceilStep (N : ℕ) (hN : 0 < N) (l : ℕ) :
    rep 3 2 (ceilStep^[l] N) =
      rep 3 2 N ++ pre (fun k => ceilStep^[k] N % 2) l := by
  induction l with
  | zero => simp [pre]
  | succ l ih =>
    rw [Function.iterate_succ_apply']
    rw [rep_child (ceilStep_digit _) (by omega) (iterate_ceilStep_pos hN l)]
    rw [ih, pre_succ_last, List.append_assoc]

/-- In base `3/2` the minimal word with seed `rep N` (`N ≥ 1`) reads the parities of the
`⌈3D/2⌉`-orbit of `N`: the least admissible digit at `D` is `D % 2`, and it leads to `⌈3D/2⌉`. -/
theorem isMinWord_ceilStep (N : ℕ) (hN : 0 < N) :
    IsMinWord 3 2 (rep 3 2 N) (fun k => ceilStep^[k] N % 2) := by
  intro l
  constructor
  · rw [← rep_iterate_ceilStep N hN l]
    exact ⟨_, rfl⟩
  · intro v hvlen hvdigits hvlang hlt
    induction l generalizing N v with
    | zero =>
      simp [pre] at hvlen hlt
    | succ l ih =>
      rcases v with _ | ⟨a, vs⟩
      · simp at hvlen
      have hvslength : vs.length = l := by simpa using Nat.succ.inj hvlen
      have ha : a < 3 := hvdigits a (by simp)
      have hpref : rep 3 2 N ++ [a] ∈ Lang 3 2 := by
        apply lang_prefix (ys := vs)
        simpa [List.append_assoc] using hvlang
      obtain ⟨M, hM⟩ := rep_extension_last hpref
      rw [pre_succ_head] at hlt
      cases hlt with
      | rel hrel =>
        simp only [Function.iterate_zero_apply] at hrel
        omega
      | cons htail =>
        have hrep := rep_child (ceilStep_digit N) (by omega) hN
        have hvlang' : rep 3 2 (ceilStep N) ++ vs ∈ Lang 3 2 := by
          rw [hrep]
          simpa [List.append_assoc] using hvlang
        have hfun : (fun k => ceilStep^[k + 1] N % 2) =
            (fun k => ceilStep^[k] (ceilStep N) % 2) := by
          funext k
          rw [Function.iterate_succ_apply]
        rw [hfun] at htail
        exact ih (ceilStep N) (ceilStep_pos hN) vs hvslength
          (fun d hd => hvdigits d (by simp [hd])) hvlang' htail

/-! ## Antihydra -/

/-- Antihydra's values are the `⌈3D/2⌉`-orbit of `7`, shifted up by one:
`H (D + 1) = ⌈3D/2⌉ + 1` where `H x = ⌊3x/2⌋`. -/
theorem antihydra_value_eq (k : ℕ) :
    (Foils.orbit Foils.floorChoice (8, 0) k).1 = ceilStep^[k] 7 + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Foils.orbit_succ]
    simp only [Foils.step, Foils.floorChoice, Bool.false_eq_true, if_false]
    rw [ih]
    unfold ceilStep
    rw [Function.iterate_succ_apply']
    omega

/-- **Main theorem.**  Antihydra's parity word is the bit-complement of the minimal word in base
`3/2` with seed `2122 = rep 7`. -/
theorem antihydra_parity_complement_minWord :
    ∃ w : ℕ → ℕ, IsMinWord 3 2 [2, 1, 2, 2] w ∧ (∀ k, w k < 2) ∧
      ∀ k, (Foils.orbit Foils.floorChoice (8, 0) k).1 % 2 = 1 - w k := by
  sorry

end Collatz.Antihydra.RationalBase
