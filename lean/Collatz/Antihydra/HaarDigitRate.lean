/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The Haar-mean base-3/2 digit rate: finite core and the spine reduction

Setting (Fornet, `antihydra-autoresearch/notes/stationary-cost-variational.md`): on `ℤ_2` the
legal step is `x ↦ (3x + d)/2` with `d ∈ {0,1,2}`, `d ≡ x (mod 2)`, cost `d`.  `V N x` is the
least cost of a legal length-`N` word from `x`; it depends only on `x mod 2^N`, and
`a_* = lim A_N/N = inf A_N/N` with `2^N A_N = ∑_{x < 2^N} V N x`.  Known:
`0.3042… ≤ a_* ≤ 0.36661`; open there: whether `a_* ≥ 1/3`.

This file holds
* the finite core: legality, `V` with its Bellman recurrence, faithfulness to the
  min-over-words definition, periodicity, and the anchors `2^4 A_4 = 31`, `2^8 A_8 = 936`;
* the weighted partition function `Z p N x` (Fornet PT1.1 with general digit weights), the
  dyadic densities `rho`, and a finite Paley–Zygmund inequality;
* the **spine reduction** of `notes/37`: for an iid digit law `p` with entropy above `log 2`,
  a uniform bound on the adjacent cross-energy `∫ ρ_N(y) ρ_N(y+1) dm` (`CrossEnergyBounded`)
  gives a uniform `L^{1+s}` bound on `ρ_N` (`moment_bound`), hence absolute continuity of
  `μ_p`, hence `a_* ≤ p₁ + 2p₂` (`haarRate_le_of_crossEnergyBounded`).  For Fornet's candidate
  `p = (18,6,1)/25` this would give `a_* ≤ 8/25 < 1/3`.

`CrossEnergyBounded` is the open crux; its evidence is in its docstring.
-/

namespace Collatz.Antihydra.HaarDigitRate

open Finset

/-! ## Legal words and the optimal cost `V` -/

/-- One step `x ↦ (3x + d)/2`; on a legal digit (`d ≡ x mod 2`) the division is exact. -/
def step (x d : ℕ) : ℕ := (3 * x + d) / 2

/-- `Legal x w`: the word `w` (chronological order) is a legal digit word from `x`: every digit
is in `{0,1,2}` and has the parity of the current state. -/
def Legal : ℕ → List ℕ → Prop
  | _, [] => True
  | x, d :: w => d ≤ 2 ∧ d % 2 = x % 2 ∧ Legal (step x d) w

/-- Cost of a word: its digit sum. -/
def cost (w : List ℕ) : ℕ := w.sum

/-- Least cost of a legal length-`N` word from `x`, by the Bellman recursion on the first digit:
an even state chooses `0` or `2`, an odd state must use `1`. -/
def V : ℕ → ℕ → ℕ
  | 0, _ => 0
  | N + 1, x =>
    if x % 2 = 0 then min (V N (step x 0)) (2 + V N (step x 2)) else 1 + V N (step x 1)

@[simp] theorem V_zero (x : ℕ) : V 0 x = 0 := rfl

theorem V_succ (N x : ℕ) : V (N + 1) x =
    if x % 2 = 0 then min (V N (step x 0)) (2 + V N (step x 2)) else 1 + V N (step x 1) := rfl

/-- Bellman recurrence on residues (Fornet AC/PT1 form), even half. -/
theorem V_succ_even (N m : ℕ) : V (N + 1) (2 * m) = min (V N (3 * m)) (2 + V N (3 * m + 1)) := by
  have h0 : step (2 * m) 0 = 3 * m := by unfold step; omega
  have h2 : step (2 * m) 2 = 3 * m + 1 := by unfold step; omega
  rw [V_succ, if_pos (by omega), h0, h2]

/-- Bellman recurrence on residues, odd half. -/
theorem V_succ_odd (N m : ℕ) : V (N + 1) (2 * m + 1) = 1 + V N (3 * m + 2) := by
  have h1 : step (2 * m + 1) 1 = 3 * m + 2 := by unfold step; omega
  rw [V_succ, if_neg (by omega), h1]

/-- Faithfulness, lower half: every legal word of length `N` costs at least `V N x`. -/
theorem V_le_cost : ∀ (w : List ℕ) (x : ℕ), Legal x w → V w.length x ≤ cost w
  | [], _, _ => by simp [cost]
  | d :: w, x, ⟨hd, hpar, hw⟩ => by
    have ih := V_le_cost w (step x d) hw
    simp only [List.length_cons, cost, List.sum_cons] at ih ⊢
    rw [V_succ]
    split_ifs with hx
    · interval_cases d
      · exact (min_le_left _ _).trans (by omega)
      · omega
      · exact (min_le_right _ _).trans (by omega)
    · interval_cases d <;> omega

/-- Faithfulness, upper half: some legal word of length `N` attains `V N x`. -/
theorem exists_legal_cost_eq_V : ∀ (N x : ℕ), ∃ w : List ℕ, w.length = N ∧ Legal x w ∧
    cost w = V N x
  | 0, x => ⟨[], rfl, trivial, rfl⟩
  | N + 1, x => by
    rw [V_succ]
    split_ifs with hx
    · obtain ⟨w0, hl0, hL0, hc0⟩ := exists_legal_cost_eq_V N (step x 0)
      obtain ⟨w2, hl2, hL2, hc2⟩ := exists_legal_cost_eq_V N (step x 2)
      rcases le_total (V N (step x 0)) (2 + V N (step x 2)) with h | h
      · refine ⟨0 :: w0, by simp [hl0], ⟨by omega, by omega, hL0⟩, ?_⟩
        rw [min_eq_left h, ← hc0]; simp [cost]
      · refine ⟨2 :: w2, by simp [hl2], ⟨le_rfl, by omega, hL2⟩, ?_⟩
        rw [min_eq_right h, ← hc2]; simp [cost]
    · obtain ⟨w1, hl1, hL1, hc1⟩ := exists_legal_cost_eq_V N (step x 1)
      refine ⟨1 :: w1, by simp [hl1], ⟨by omega, by omega, hL1⟩, ?_⟩
      rw [← hc1]; simp [cost]

/-- `V N x` is the minimum over legal length-`N` words (both halves together). -/
theorem V_isLeast (N x : ℕ) :
    IsLeast {c | ∃ w : List ℕ, w.length = N ∧ Legal x w ∧ cost w = c} (V N x) := by
  refine ⟨exists_legal_cost_eq_V N x, ?_⟩
  rintro c ⟨w, rfl, hL, rfl⟩
  exact V_le_cost w x hL

/-- The greedy bound `V N x ≤ N`. -/
theorem V_le (N : ℕ) : ∀ x, V N x ≤ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    intro x
    rw [V_succ]
    split_ifs
    · exact (min_le_left _ _).trans ((ih _).trans (Nat.le_succ N))
    · have := ih (step x 1); omega

/-- `V N x` depends only on `x mod 2^N`. -/
theorem V_add_pow_mul (N : ℕ) : ∀ x k, V N (x + 2 ^ N * k) = V N x := by
  induction N with
  | zero => simp
  | succ N ih =>
    intro x k
    have hK : 2 ^ (N + 1) * k = 2 * (2 ^ N * k) := by ring
    have h3 : 2 ^ N * (3 * k) = 3 * (2 ^ N * k) := by ring
    have hpar : (x + 2 ^ (N + 1) * k) % 2 = x % 2 := by
      rw [hK]; omega
    have hs : ∀ d, d % 2 = x % 2 → step (x + 2 ^ (N + 1) * k) d = step x d + 2 ^ N * (3 * k) := by
      intro d hd; unfold step; rw [hK, h3]; generalize 2 ^ N * k = K; omega
    rw [V_succ, V_succ, hpar]
    split_ifs with hx
    · rw [hs 0 (by omega), hs 2 (by omega), ih, ih]
    · rw [hs 1 (by omega), ih]

/-- `V N x = V N (x % 2^N)`. -/
theorem V_mod (N x : ℕ) : V N (x % 2 ^ N) = V N x := by
  conv_rhs => rw [← Nat.mod_add_div x (2 ^ N)]
  rw [V_add_pow_mul]

/-- `sumTo f n = ∑_{x < n} f x`, by structural recursion (kernel-friendly for `decide`). -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ x ∈ range n, f x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ← ih]; rfl

/-- `2^N A_N = ∑_{x < 2^N} V N x`. -/
def sumV (N : ℕ) : ℕ := sumTo (V N) (2 ^ N)

set_option maxRecDepth 100000 in
/-- Anchor: `2^4 A_4 = 31`. -/
theorem sumV_four : sumV 4 = 31 := by decide

set_option maxRecDepth 100000 in
/-- Anchor: `2^8 A_8 = 936`. -/
theorem sumV_eight : sumV 8 = 936 := by decide

/-! ## Weighted partition functions and dyadic densities -/

/-- Weighted partition function `Z p N x = ∑_{legal w, |w| = N} ∏ p(w_j)` (Fornet PT1.1 with
`p d = t^d`), by the first-digit recursion. -/
noncomputable def Z (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | N + 1, x =>
    if x % 2 = 0 then p 0 * Z p N (step x 0) + p 2 * Z p N (step x 2)
    else p 1 * Z p N (step x 1)

theorem Z_succ (p : ℕ → ℝ) (N x : ℕ) : Z p (N + 1) x =
    if x % 2 = 0 then p 0 * Z p N (step x 0) + p 2 * Z p N (step x 2)
    else p 1 * Z p N (step x 1) := rfl

/-- `Z p N x` depends only on `x mod 2^N`. -/
theorem Z_add_pow_mul (p : ℕ → ℝ) (N : ℕ) : ∀ x k, Z p N (x + 2 ^ N * k) = Z p N x := by
  induction N with
  | zero => intro x k; rfl
  | succ N ih =>
    intro x k
    have hK : 2 ^ (N + 1) * k = 2 * (2 ^ N * k) := by ring
    have h3 : 2 ^ N * (3 * k) = 3 * (2 ^ N * k) := by ring
    have hpar : (x + 2 ^ (N + 1) * k) % 2 = x % 2 := by
      rw [hK]; omega
    have hs : ∀ d, d % 2 = x % 2 → step (x + 2 ^ (N + 1) * k) d = step x d + 2 ^ N * (3 * k) := by
      intro d hd; unfold step; rw [hK, h3]; generalize 2 ^ N * k = K; omega
    rw [Z_succ, Z_succ, hpar]
    split_ifs with hx
    · rw [hs 0 (by omega), hs 2 (by omega), ih, ih]
    · rw [hs 1 (by omega), ih]

theorem Z_nonneg (p : ℕ → ℝ) (hp : ∀ d, 0 ≤ p d) (N : ℕ) : ∀ x, 0 ≤ Z p N x := by
  induction N with
  | zero => intro x; simp [Z]
  | succ N ih =>
    intro x; rw [Z_succ]
    split_ifs
    · exact add_nonneg (mul_nonneg (hp 0) (ih _)) (mul_nonneg (hp 2) (ih _))
    · exact mul_nonneg (hp 1) (ih _)

/-- The dyadic density `ρ_N(x) = 2^N μ_p(x + 2^N ℤ_2) = 2^N Z p N x` of the iid self-similar law
`μ_p` (Fornet PT1.2 / IC1.2). -/
noncomputable def rho (p : ℕ → ℝ) (N x : ℕ) : ℝ := 2 ^ N * Z p N x

/-- Haar average over residues mod `2^N`. -/
noncomputable def haarAvg (N : ℕ) (f : ℕ → ℝ) : ℝ := (∑ r ∈ range (2 ^ N), f r) / 2 ^ N

/-- **Adjacent cross-energy** `∫ ρ_N(y) ρ_N(y+1) dm(y)`: the `L²` mutual energy of `μ_p` and its
unit translate, equivalently `2^N · P(X' − X ≡ 1 mod 2^N)` for independent `X, X' ∼ μ_p`. -/
noncomputable def crossEnergy (p : ℕ → ℝ) (N : ℕ) : ℝ :=
  haarAvg N (fun r => rho p N r * rho p N (r + 1))

/-- The `(1+s)`-th moment `∫ ρ_N^{1+s} dm = E_{μ_p}[ρ_N^s]`. -/
noncomputable def moment (p : ℕ → ℝ) (s : ℝ) (N : ℕ) : ℝ :=
  haarAvg N (fun r => rho p N r ^ (1 + s))

/-- A probability vector on the digits `{0,1,2}` (values at `d ≥ 3` are irrelevant). -/
def IsDigitLaw (p : ℕ → ℝ) : Prop := (∀ d, 0 ≤ p d) ∧ p 0 + p 1 + p 2 = 1

/-- Spine ratio `q(s) = 2^s ∑_d p_d^{1+s}`.  `q(s) < 1` for small `s > 0` iff the entropy of
`p` exceeds `log 2` (the derivative at `s = 0` is `log 2 − H(p)`). -/
noncomputable def spineRatio (p : ℕ → ℝ) (s : ℝ) : ℝ :=
  2 ^ s * (p 0 ^ (1 + s) + p 1 ^ (1 + s) + p 2 ^ (1 + s))

/-- Sibling weight `r(s) = 2^s (p_0 p_2^s + p_2 p_0^s)`. -/
noncomputable def siblingWeight (p : ℕ → ℝ) (s : ℝ) : ℝ :=
  2 ^ s * (p 0 * p 2 ^ s + p 2 * p 0 ^ s)

/-- Fornet's candidate digit law `(18, 6, 1)/25`, of mean cost `8/25`. -/
noncomputable def candidate : ℕ → ℝ
  | 0 => 18 / 25
  | 1 => 6 / 25
  | 2 => 1 / 25
  | _ => 0

theorem candidate_isDigitLaw : IsDigitLaw candidate := by
  refine ⟨fun d => ?_, ?_⟩
  · match d with
    | 0 => show (0 : ℝ) ≤ 18 / 25; norm_num
    | 1 => show (0 : ℝ) ≤ 6 / 25; norm_num
    | 2 => show (0 : ℝ) ≤ 1 / 25; norm_num
    | _ + 3 => exact le_refl (0 : ℝ)
  · show (18 / 25 : ℝ) + 6 / 25 + 1 / 25 = 1; norm_num

theorem candidate_cost : candidate 1 + 2 * candidate 2 = 8 / 25 := by
  show (6 / 25 : ℝ) + 2 * (1 / 25) = 8 / 25; norm_num

/-! ## The one-step moment recursion

`moment_bound` is the unrolled form of `M_{N+1} ≤ q M_N + r Λ_N^s` (`moment_succ_le`).  The
first digit splits `ρ_{N+1}(2m) = 2p₀ρ_N(3m) + 2p₂ρ_N(3m+1)` and `ρ_{N+1}(2m+1) = 2p₁ρ_N(3m+2)`;
subadditivity of `x ↦ x^s` separates the two even branches, `m ↦ 3m + c` permutes residues mod
`2^N`, and concave Jensen under the probability weights `Z p N r` bounds the two cross terms by
`Λ_N^s`. -/

/-- Reindexing a `2^N`-periodic sum by an odd affine map `m ↦ a m + c`. -/
theorem sum_range_pow_affine {β : Type*} [AddCommMonoid β] (N a c : ℕ) (ha : a % 2 = 1)
    (g : ℕ → β) (hg : ∀ x k, g (x + 2 ^ N * k) = g x) :
    ∑ m ∈ range (2 ^ N), g (a * m + c) = ∑ r ∈ range (2 ^ N), g r := by
  have hmod : ∀ x, g (x % 2 ^ N) = g x := fun x => by
    conv_rhs => rw [← Nat.mod_add_div x (2 ^ N)]
    rw [hg]
  set f : ℕ → ℕ := fun m => (a * m + c) % 2 ^ N with hf
  have hinj : Set.InjOn f (range (2 ^ N)) := by
    intro m hm m' hm' h
    simp only [coe_range, Set.mem_Iio] at hm hm'
    have h2 : a * m ≡ a * m' [MOD 2 ^ N] := Nat.ModEq.add_right_cancel' c h
    have hcop : Nat.gcd (2 ^ N) a = 1 :=
      Nat.Coprime.pow_left N (Nat.coprime_two_left.2 (Nat.odd_iff.2 ha))
    have h3 := Nat.ModEq.cancel_left_of_coprime hcop h2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hm'] at h3
  have himg : (range (2 ^ N)).image f = range (2 ^ N) := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨m, -, rfl⟩ := mem_image.1 hy
      exact mem_range.2 (Nat.mod_lt _ (by positivity))
    · rw [card_image_of_injOn hinj]
  conv_rhs => rw [← himg]
  rw [sum_image hinj]
  exact sum_congr rfl fun m _ => (hmod _).symm

/-- Split a sum over `x < 2n` into even and odd halves. -/
theorem sum_range_two_mul {β : Type*} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) :
    ∑ x ∈ range (2 * n), f x = ∑ m ∈ range n, (f (2 * m) + f (2 * m + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    abel

theorem Z_succ_even (p : ℕ → ℝ) (N m : ℕ) :
    Z p (N + 1) (2 * m) = p 0 * Z p N (3 * m) + p 2 * Z p N (3 * m + 1) := by
  have h0 : step (2 * m) 0 = 3 * m := by unfold step; omega
  have h2 : step (2 * m) 2 = 3 * m + 1 := by unfold step; omega
  rw [Z_succ, if_pos (by omega), h0, h2]

theorem Z_succ_odd (p : ℕ → ℝ) (N m : ℕ) : Z p (N + 1) (2 * m + 1) = p 1 * Z p N (3 * m + 2) := by
  have h1 : step (2 * m + 1) 1 = 3 * m + 2 := by unfold step; omega
  rw [Z_succ, if_neg (by omega), h1]

/-- Total mass: `∑_{r < 2^N} Z p N r = (p₀ + p₁ + p₂)^N`. -/
theorem sum_Z (p : ℕ → ℝ) (N : ℕ) : ∑ r ∈ range (2 ^ N), Z p N r = (p 0 + p 1 + p 2) ^ N := by
  induction N with
  | zero => simp [Z]
  | succ N ih =>
    have hper := Z_add_pow_mul p N
    have e0 := sum_range_pow_affine N 3 0 rfl (Z p N) hper
    have e1 := sum_range_pow_affine N 3 1 rfl (Z p N) hper
    have e2 := sum_range_pow_affine N 3 2 rfl (Z p N) hper
    simp only [add_zero] at e0
    rw [pow_succ', sum_range_two_mul]
    simp only [Z_succ_even, Z_succ_odd, sum_add_distrib, ← mul_sum, e0, e1, e2, ih]
    ring

theorem rho_nonneg (p : ℕ → ℝ) (hp : ∀ d, 0 ≤ p d) (N x : ℕ) : 0 ≤ rho p N x :=
  mul_nonneg (by positivity) (Z_nonneg p hp N x)

theorem rho_add_pow_mul (p : ℕ → ℝ) (N x k : ℕ) : rho p N (x + 2 ^ N * k) = rho p N x := by
  simp only [rho, Z_add_pow_mul]

theorem rho_succ_even (p : ℕ → ℝ) (N m : ℕ) :
    rho p (N + 1) (2 * m) = 2 * p 0 * rho p N (3 * m) + 2 * p 2 * rho p N (3 * m + 1) := by
  simp only [rho, Z_succ_even, pow_succ]; ring

theorem rho_succ_odd (p : ℕ → ℝ) (N m : ℕ) :
    rho p (N + 1) (2 * m + 1) = 2 * p 1 * rho p N (3 * m + 2) := by
  simp only [rho, Z_succ_odd, pow_succ]; ring

theorem rpow_one_add_eq {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) : x ^ (1 + s) = x * x ^ s := by
  rw [Real.rpow_add' hx (by linarith), Real.rpow_one]

/-- Concave Jensen for a shifted cross term: if `w ≥ 0` sums to `1` over residues then
`∑ w r · y_r^s ≤ (∑ w r · y_r)^s`. -/
theorem jensen_rpow (t : Finset ℕ) (w y : ℕ → ℝ) (hw : ∀ r ∈ t, 0 ≤ w r) (h1 : ∑ r ∈ t, w r = 1)
    (hy : ∀ r ∈ t, 0 ≤ y r) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ r ∈ t, w r * y r ^ s ≤ (∑ r ∈ t, w r * y r) ^ s := by
  have := (Real.concaveOn_rpow hs0 hs1).le_map_sum hw h1 (fun r hr => Set.mem_Ici.2 (hy r hr))
  simpa only [smul_eq_mul] using this

/-- The two cross terms of the one-step recursion are bounded by `Λ_N^s`. -/
theorem cross_terms_le (p : ℕ → ℝ) (hp : IsDigitLaw p) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (N : ℕ) :
    (∑ r ∈ range (2 ^ N), rho p N r * rho p N (r + 1) ^ s) / 2 ^ N ≤ crossEnergy p N ^ s ∧
    (∑ r ∈ range (2 ^ N), rho p N (r + 1) * rho p N r ^ s) / 2 ^ N ≤ crossEnergy p N ^ s := by
  have hP : (0 : ℝ) < 2 ^ N := by positivity
  have hZ1 : ∑ r ∈ range (2 ^ N), Z p N r = 1 := by rw [sum_Z, hp.2, one_pow]
  have hZ1' : ∑ r ∈ range (2 ^ N), Z p N (r + 1) = 1 := by
    have := sum_range_pow_affine N 1 1 rfl (Z p N) (Z_add_pow_mul p N)
    simp only [one_mul] at this
    rw [this, hZ1]
  have hrho : ∀ r, rho p N r / 2 ^ N = Z p N r := fun r => by
    rw [rho, mul_div_cancel_left₀ _ hP.ne']
  have hΛ : crossEnergy p N = ∑ r ∈ range (2 ^ N), Z p N r * rho p N (r + 1) := by
    rw [crossEnergy, haarAvg, sum_div]
    exact sum_congr rfl fun r _ => by rw [← hrho, div_mul_eq_mul_div]
  have hΛ' : crossEnergy p N = ∑ r ∈ range (2 ^ N), Z p N (r + 1) * rho p N r := by
    rw [crossEnergy, haarAvg, sum_div]
    exact sum_congr rfl fun r _ => by rw [← hrho, div_mul_eq_mul_div, mul_comm]
  have hnn := rho_nonneg p hp.1 N
  have hZnn := Z_nonneg p hp.1 N
  constructor
  · rw [hΛ, sum_div]
    calc ∑ r ∈ range (2 ^ N), rho p N r * rho p N (r + 1) ^ s / 2 ^ N
        = ∑ r ∈ range (2 ^ N), Z p N r * rho p N (r + 1) ^ s :=
          sum_congr rfl fun r _ => by rw [← hrho, div_mul_eq_mul_div]
      _ ≤ _ := jensen_rpow _ _ _ (fun r _ => hZnn r) hZ1 (fun r _ => hnn _) s hs0.le hs1
  · rw [hΛ', sum_div]
    calc ∑ r ∈ range (2 ^ N), rho p N (r + 1) * rho p N r ^ s / 2 ^ N
        = ∑ r ∈ range (2 ^ N), Z p N (r + 1) * rho p N r ^ s :=
          sum_congr rfl fun r _ => by rw [← hrho, div_mul_eq_mul_div]
      _ ≤ _ := jensen_rpow _ _ _ (fun r _ => hZnn _) hZ1' (fun r _ => hnn _) s hs0.le hs1

/-- **One-step moment recursion** `M_{N+1} ≤ q M_N + r Λ_N^s` (notes/37 Theorem A, one digit). -/
theorem moment_succ_le (p : ℕ → ℝ) (hp : IsDigitLaw p) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (N : ℕ) : moment p s (N + 1) ≤
      spineRatio p s * moment p s N + siblingWeight p s * crossEnergy p N ^ s := by
  have hp0 := hp.1 0
  have hp1 := hp.1 1
  have hp2 := hp.1 2
  have hP : (0 : ℝ) < 2 ^ N := by positivity
  have hm : ∀ M, moment p s M = (∑ r ∈ range (2 ^ M), rho p M r * rho p M r ^ s) / 2 ^ M := by
    intro M; rw [moment, haarAvg]
    congr 1; exact sum_congr rfl fun r _ => rpow_one_add_eq (rho_nonneg p hp.1 M r) hs0
  obtain ⟨hCp, hCm⟩ := cross_terms_le p hp s hs0 hs1 N
  set ρ := rho p N with hρdef
  have hnn : ∀ x, 0 ≤ ρ x := rho_nonneg p hp.1 N
  set S := ∑ r ∈ range (2 ^ N), ρ r * ρ r ^ s with hS
  set Cp := ∑ r ∈ range (2 ^ N), ρ r * ρ (r + 1) ^ s with hCpdef
  set Cm := ∑ r ∈ range (2 ^ N), ρ (r + 1) * ρ r ^ s with hCmdef
  have hper : ∀ x k, ρ (x + 2 ^ N * k) = ρ x := fun x k => rho_add_pow_mul p N x k
  have hper1 : ∀ x k, ρ (x + 2 ^ N * k) * ρ (x + 2 ^ N * k) ^ s = ρ x * ρ x ^ s := by
    intro x k; rw [hper]
  have hperp : ∀ x k, ρ (x + 2 ^ N * k) * ρ (x + 2 ^ N * k + 1) ^ s = ρ x * ρ (x + 1) ^ s := by
    intro x k; rw [show x + 2 ^ N * k + 1 = (x + 1) + 2 ^ N * k by ring, hper, hper]
  have hperm : ∀ x k, ρ (x + 2 ^ N * k + 1) * ρ (x + 2 ^ N * k) ^ s = ρ (x + 1) * ρ x ^ s := by
    intro x k; rw [show x + 2 ^ N * k + 1 = (x + 1) + 2 ^ N * k by ring, hper, hper]
  have e0 := sum_range_pow_affine N 3 0 rfl (fun x => ρ x * ρ x ^ s) hper1
  have e1 := sum_range_pow_affine N 3 1 rfl (fun x => ρ x * ρ x ^ s) hper1
  have e2 := sum_range_pow_affine N 3 2 rfl (fun x => ρ x * ρ x ^ s) hper1
  have ep := sum_range_pow_affine N 3 0 rfl (fun x => ρ x * ρ (x + 1) ^ s) hperp
  have em := sum_range_pow_affine N 3 0 rfl (fun x => ρ (x + 1) * ρ x ^ s) hperm
  simp only [add_zero] at e0 ep em
  beta_reduce at e1 e2
  -- pointwise bound on one even/odd pair
  have hpt : ∀ m, rho p (N + 1) (2 * m) * rho p (N + 1) (2 * m) ^ s +
      rho p (N + 1) (2 * m + 1) * rho p (N + 1) (2 * m + 1) ^ s ≤
      2 * p 0 * (2 * p 0) ^ s * (ρ (3 * m) * ρ (3 * m) ^ s) +
      2 * p 2 * (2 * p 2) ^ s * (ρ (3 * m + 1) * ρ (3 * m + 1) ^ s) +
      2 * p 1 * (2 * p 1) ^ s * (ρ (3 * m + 2) * ρ (3 * m + 2) ^ s) +
      2 * p 0 * (2 * p 2) ^ s * (ρ (3 * m) * ρ (3 * m + 1) ^ s) +
      2 * p 2 * (2 * p 0) ^ s * (ρ (3 * m + 1) * ρ (3 * m) ^ s) := by
    intro m
    rw [rho_succ_even, rho_succ_odd]
    have ha : 0 ≤ 2 * p 0 * ρ (3 * m) := mul_nonneg (by positivity) (hnn _)
    have hb : 0 ≤ 2 * p 2 * ρ (3 * m + 1) := mul_nonneg (by positivity) (hnn _)
    have hsub := Real.rpow_add_le_add_rpow ha hb hs0.le hs1
    have f0 : (2 * p 0 * ρ (3 * m)) ^ s = (2 * p 0) ^ s * ρ (3 * m) ^ s :=
      Real.mul_rpow (by positivity) (hnn _)
    have f2 : (2 * p 2 * ρ (3 * m + 1)) ^ s = (2 * p 2) ^ s * ρ (3 * m + 1) ^ s :=
      Real.mul_rpow (by positivity) (hnn _)
    have f1 : (2 * p 1 * ρ (3 * m + 2)) ^ s = (2 * p 1) ^ s * ρ (3 * m + 2) ^ s :=
      Real.mul_rpow (by positivity) (hnn _)
    calc (2 * p 0 * ρ (3 * m) + 2 * p 2 * ρ (3 * m + 1)) *
          (2 * p 0 * ρ (3 * m) + 2 * p 2 * ρ (3 * m + 1)) ^ s +
          2 * p 1 * ρ (3 * m + 2) * (2 * p 1 * ρ (3 * m + 2)) ^ s
        ≤ (2 * p 0 * ρ (3 * m) + 2 * p 2 * ρ (3 * m + 1)) *
          ((2 * p 0 * ρ (3 * m)) ^ s + (2 * p 2 * ρ (3 * m + 1)) ^ s) +
          2 * p 1 * ρ (3 * m + 2) * (2 * p 1 * ρ (3 * m + 2)) ^ s := by
          gcongr
      _ = _ := by rw [f0, f2, f1]; ring
  have hsum : ∑ x ∈ range (2 ^ (N + 1)), rho p (N + 1) x * rho p (N + 1) x ^ s ≤
      2 * p 0 * (2 * p 0) ^ s * S + 2 * p 2 * (2 * p 2) ^ s * S + 2 * p 1 * (2 * p 1) ^ s * S +
      2 * p 0 * (2 * p 2) ^ s * Cp + 2 * p 2 * (2 * p 0) ^ s * Cm := by
    rw [pow_succ', sum_range_two_mul]
    refine (sum_le_sum fun m _ => hpt m).trans (le_of_eq ?_)
    simp only [sum_add_distrib, ← mul_sum, e0, e1, e2, ep, em]
    rfl
  have g0 : (2 * p 0) ^ s = 2 ^ s * p 0 ^ s := Real.mul_rpow (by norm_num) hp0
  have g1 : (2 * p 1) ^ s = 2 ^ s * p 1 ^ s := Real.mul_rpow (by norm_num) hp1
  have g2 : (2 * p 2) ^ s = 2 ^ s * p 2 ^ s := Real.mul_rpow (by norm_num) hp2
  have h2s : (0 : ℝ) ≤ 2 ^ s := by positivity
  have hq : spineRatio p s * moment p s N =
      2 ^ s * (p 0 * p 0 ^ s + p 1 * p 1 ^ s + p 2 * p 2 ^ s) * (S / 2 ^ N) := by
    rw [spineRatio, hm, rpow_one_add_eq hp0 hs0, rpow_one_add_eq hp1 hs0,
      rpow_one_add_eq hp2 hs0]
  rw [hm, hq, siblingWeight]
  calc (∑ x ∈ range (2 ^ (N + 1)), rho p (N + 1) x * rho p (N + 1) x ^ s) / 2 ^ (N + 1)
      ≤ (2 * p 0 * (2 * p 0) ^ s * S + 2 * p 2 * (2 * p 2) ^ s * S +
          2 * p 1 * (2 * p 1) ^ s * S + 2 * p 0 * (2 * p 2) ^ s * Cp +
          2 * p 2 * (2 * p 0) ^ s * Cm) / 2 ^ (N + 1) := by gcongr
    _ = 2 ^ s * (p 0 * p 0 ^ s + p 1 * p 1 ^ s + p 2 * p 2 ^ s) * (S / 2 ^ N) +
        2 ^ s * p 0 * p 2 ^ s * (Cp / 2 ^ N) + 2 ^ s * p 2 * p 0 ^ s * (Cm / 2 ^ N) := by
      rw [g0, g1, g2, pow_succ]; field_simp; ring
    _ ≤ 2 ^ s * (p 0 * p 0 ^ s + p 1 * p 1 ^ s + p 2 * p 2 ^ s) * (S / 2 ^ N) +
        2 ^ s * p 0 * p 2 ^ s * crossEnergy p N ^ s +
        2 ^ s * p 2 * p 0 ^ s * crossEnergy p N ^ s := by gcongr
    _ = _ := by ring

/-! ## Theorem B ingredients: runs, block commitment, Chernoff, Hölder -/

/-- The state reached from `x` after the word `w`. -/
def run : ℕ → List ℕ → ℕ
  | x, [] => x
  | x, d :: w => run (step x d) w

/-- A legal word from `x` is legal from every `x + 2^|w| u`, and its endpoint moves by `3^|w| u`
(Fornet OE1: block endpoints of a residue class are Haar). -/
theorem legal_run_add : ∀ (w : List ℕ) (x u : ℕ), Legal x w →
    Legal (x + 2 ^ w.length * u) w ∧ run (x + 2 ^ w.length * u) w = run x w + 3 ^ w.length * u
  | [], x, u, _ => by simp [Legal, run]
  | d :: w, x, u, ⟨hd, hpar, hw⟩ => by
    have hs : step (x + 2 ^ (w.length + 1) * u) d = step x d + 2 ^ w.length * (3 * u) := by
      unfold step
      have : 2 ^ (w.length + 1) * u = 2 * (2 ^ w.length * u) := by ring
      rw [this, show 2 ^ w.length * (3 * u) = 3 * (2 ^ w.length * u) by ring]
      generalize 2 ^ w.length * u = K
      omega
    obtain ⟨h1, h2⟩ := legal_run_add w (step x d) (3 * u) hw
    simp only [List.length_cons]
    refine ⟨⟨hd, ?_, ?_⟩, ?_⟩
    · rw [show 2 ^ (w.length + 1) * u = 2 * (2 ^ w.length * u) by ring]; omega
    · rw [hs]; exact h1
    · simp only [run]; rw [hs, h2]; ring

theorem legal_append : ∀ (w w' : List ℕ) (x : ℕ), Legal x w → Legal (run x w) w' →
    Legal x (w ++ w')
  | [], _, _, _, h => h
  | d :: w, w', x, ⟨hd, hpar, hw⟩, h => ⟨hd, hpar, legal_append w w' (step x d) hw h⟩

/-- Concatenation: `V_{|w|+M}(x) ≤ cost w + V_M(run x w)` for a legal `w`. -/
theorem V_add_le (w : List ℕ) (x M : ℕ) (h : Legal x w) :
    V (w.length + M) x ≤ cost w + V M (run x w) := by
  obtain ⟨w', hl, hL, hc⟩ := exists_legal_cost_eq_V M (run x w)
  have h2 := V_le_cost (w ++ w') x (legal_append w w' x h hL)
  rw [List.length_append, hl] at h2
  rw [← hc]
  simpa [cost, List.sum_append] using h2

/-- `V (N + r) x ≤ V N x + r`. -/
theorem V_add_le_add (N r x : ℕ) : V (N + r) x ≤ V N x + r := by
  obtain ⟨w, hl, hL, hc⟩ := exists_legal_cost_eq_V N x
  have := V_add_le w x r hL
  rw [hl, hc] at this
  exact this.trans (by have := V_le r (run x w); omega)

/-- An optimal length-`L` word from the residue `r`. -/
noncomputable def wopt (L r : ℕ) : List ℕ := Classical.choose (exists_legal_cost_eq_V L r)

theorem wopt_spec (L r : ℕ) :
    (wopt L r).length = L ∧ Legal r (wopt L r) ∧ cost (wopt L r) = V L r :=
  Classical.choose_spec (exists_legal_cost_eq_V L r)

/-- Block commitment: the start of the next length-`L` block after the optimal word of the
current residue. -/
noncomputable def nxt (L x : ℕ) : ℕ := run x (wopt L (x % 2 ^ L))

theorem nxt_eq (L x : ℕ) :
    nxt L x = run (x % 2 ^ L) (wopt L (x % 2 ^ L)) + 3 ^ L * (x / 2 ^ L) := by
  obtain ⟨hl, hL, -⟩ := wopt_spec L (x % 2 ^ L)
  have := (legal_run_add _ (x % 2 ^ L) (x / 2 ^ L) hL).2
  rw [hl, Nat.mod_add_div] at this
  exact this

theorem nxt_add (L x u : ℕ) : nxt L (x + 2 ^ L * u) = nxt L x + 3 ^ L * u := by
  have h1 : (x + 2 ^ L * u) % 2 ^ L = x % 2 ^ L := by simp
  have h2 : (x + 2 ^ L * u) / 2 ^ L = x / 2 ^ L + u := by
    rw [Nat.add_mul_div_left _ _ (by positivity)]
  rw [nxt_eq, nxt_eq, h1, h2]; ring

theorem V_add_le_nxt (L M x : ℕ) : V (L + M) x ≤ V L x + V M (nxt L x) := by
  obtain ⟨hl, hL, hc⟩ := wopt_spec L (x % 2 ^ L)
  have hL' : Legal x (wopt L (x % 2 ^ L)) := by
    have := (legal_run_add _ (x % 2 ^ L) (x / 2 ^ L) hL).1
    rwa [hl, Nat.mod_add_div] at this
  have := V_add_le _ x M hL'
  rwa [hl, hc, V_mod] at this

/-- Split a sum over `x < a b` along `x = r + a u`. -/
theorem sum_range_mul_split {β : Type*} [AddCommMonoid β] (f : ℕ → β) (a b : ℕ) :
    ∑ x ∈ range (a * b), f x = ∑ u ∈ range b, ∑ r ∈ range a, f (r + a * u) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [mul_add, mul_one, sum_range_add, ih, sum_range_succ]
    congr 1
    exact sum_congr rfl fun r _ => by rw [add_comm]

/-- **Block independence.**  Under the uniform law on residues mod `2^{L+M}`, the residue
mod `2^L` and the next block start mod `2^M` are independent and uniform. -/
theorem sum_block {β : Type*} [AddCommMonoid β] (L M : ℕ) (F : ℕ → ℕ → β)
    (hF : ∀ r y k, F r (y + 2 ^ M * k) = F r y) :
    ∑ x ∈ range (2 ^ (L + M)), F (x % 2 ^ L) (nxt L x) =
      ∑ r ∈ range (2 ^ L), ∑ y ∈ range (2 ^ M), F r y := by
  rw [pow_add, sum_range_mul_split, sum_comm]
  refine sum_congr rfl fun r hr => ?_
  have hr' : r < 2 ^ L := mem_range.1 hr
  have h1 : ∀ u, (r + 2 ^ L * u) % 2 ^ L = r := fun u => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
  simp only [h1, nxt_add]
  have hodd : 3 ^ L % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
  have := sum_range_pow_affine M (3 ^ L) (nxt L r) hodd (F r) (hF r)
  rw [← this]
  exact sum_congr rfl fun u _ => by rw [add_comm]


/-- Cost of `q` committed optimal blocks of length `L` from `x`. -/
noncomputable def blockCost (L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | q + 1, x => V L x + blockCost L q (nxt L x)

theorem V_le_blockCost (L : ℕ) : ∀ q x, V (q * L) x ≤ blockCost L q x
  | 0, x => by simp [blockCost]
  | q + 1, x => by
    have h1 := V_add_le_nxt L (q * L) x
    have h2 := V_le_blockCost L q (nxt L x)
    rw [show (q + 1) * L = L + q * L by ring]
    simp only [blockCost]
    omega

theorem blockCost_add (L : ℕ) : ∀ q x k, blockCost L q (x + 2 ^ (q * L) * k) = blockCost L q x
  | 0, x, k => rfl
  | q + 1, x, k => by
    simp only [blockCost]
    have e : 2 ^ ((q + 1) * L) * k = 2 ^ L * (2 ^ (q * L) * k) := by ring
    rw [e, V_add_pow_mul, nxt_add,
      show 3 ^ L * (2 ^ (q * L) * k) = 2 ^ (q * L) * (3 ^ L * k) by ring, blockCost_add L q]

theorem sumV_eq (N : ℕ) : (sumV N : ℝ) = ∑ x ∈ range (2 ^ N), (V N x : ℝ) := by
  rw [sumV, sumTo_eq]; push_cast; rfl

/-- Sum of a doubly indexed square, expanded. -/
theorem sum_sum_add_sq (R Y : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ r ∈ R, ∑ y ∈ Y, (f r + g y) ^ 2 =
      Y.card * ∑ r ∈ R, f r ^ 2 + 2 * (∑ r ∈ R, f r) * (∑ y ∈ Y, g y) +
        R.card * ∑ y ∈ Y, g y ^ 2 := by
  simp only [add_sq, sum_add_distrib, ← sum_mul, ← mul_sum, sum_const, nsmul_eq_mul]

/-- Mean of the block cost: `∑_x blockCost = q 2^{qL} a`, `a = A_L`. -/
theorem sum_blockCost (L : ℕ) : ∀ q, ∑ x ∈ range (2 ^ (q * L)), (blockCost L q x : ℝ) =
    q * 2 ^ (q * L) * ((sumV L : ℝ) / 2 ^ L)
  | 0 => by simp [blockCost]
  | q + 1 => by
    have hP : (2 : ℝ) ^ L ≠ 0 := by positivity
    rw [show (q + 1) * L = L + q * L by ring]
    simp only [blockCost]
    push_cast
    have := sum_block L (q * L) (fun r y => (V L r : ℝ) + (blockCost L q y : ℝ))
      (fun r y k => by simp only [blockCost_add])
    simp only [V_mod] at this
    rw [this]
    simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
    rw [← sumV_eq, sum_blockCost L q]
    push_cast
    field_simp
    ring

/-- Variance of the block cost: `∑_x (blockCost − q a)² ≤ q 2^{qL} L²`. -/
theorem sum_sq_blockCost (L : ℕ) : ∀ q, ∑ x ∈ range (2 ^ (q * L)),
    ((blockCost L q x : ℝ) - q * ((sumV L : ℝ) / 2 ^ L)) ^ 2 ≤ (q : ℝ) * 2 ^ (q * L) * (L : ℝ) ^ 2
  | 0 => by simp [blockCost]
  | q + 1 => by
    set a := (sumV L : ℝ) / 2 ^ L with ha
    have hP : (2 : ℝ) ^ L ≠ 0 := by positivity
    rw [show (q + 1) * L = L + q * L by ring]
    simp only [blockCost]
    push_cast
    have := sum_block L (q * L)
      (fun r y => (((V L r : ℝ) - a) + ((blockCost L q y : ℝ) - q * a)) ^ 2)
      (fun r y k => by simp only [blockCost_add])
    simp only [V_mod] at this
    have e : ∀ x, ((V L x : ℝ) + (blockCost L q (nxt L x) : ℝ) - (q + 1) * a) ^ 2 =
        (((V L x : ℝ) - a) + ((blockCost L q (nxt L x) : ℝ) - q * a)) ^ 2 := fun x => by ring
    simp only [e]
    rw [this, sum_sum_add_sq]
    have h0 : ∑ r ∈ range (2 ^ L), ((V L r : ℝ) - a) = 0 := by
      rw [sum_sub_distrib, ← sumV_eq, sum_const, card_range, nsmul_eq_mul, ha]
      push_cast; field_simp; ring
    have h1 : ∑ r ∈ range (2 ^ L), ((V L r : ℝ) - a) ^ 2 ≤ 2 ^ L * L ^ 2 := by
      have hle : ∀ r ∈ range (2 ^ L),
          ((V L r : ℝ) - a) ^ 2 ≤ (V L r : ℝ) ^ 2 - 2 * a * V L r + a ^ 2 :=
        fun r _ => le_of_eq (by ring)
      refine (sum_le_sum hle).trans ?_
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sumV_eq, sum_const, card_range,
        nsmul_eq_mul]
      have hV : ∀ r ∈ range (2 ^ L), (V L r : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := fun r _ => by
        have := V_le L r
        have : (V L r : ℝ) ≤ L := by exact_mod_cast this
        nlinarith [(Nat.cast_nonneg (V L r) : (0 : ℝ) ≤ V L r)]
      have hs := sum_le_sum hV
      rw [sum_const, card_range, nsmul_eq_mul] at hs
      have : (sumV L : ℝ) = 2 ^ L * a := by rw [ha]; field_simp
      push_cast at hs ⊢
      rw [this]
      nlinarith [sq_nonneg a, (by positivity : (0 : ℝ) < 2 ^ L)]
    have h2 := sum_sq_blockCost L q
    rw [h0]
    simp only [card_range]
    push_cast
    rw [pow_add]
    nlinarith [(by positivity : (0 : ℝ) < 2 ^ L), (by positivity : (0 : ℝ) < 2 ^ (q * L))]

/-- Haar-mean subadditivity along multiples: `A_{qL} ≤ q A_L`. -/
theorem A_mul_le (L q : ℕ) :
    (sumV (q * L) : ℝ) / 2 ^ (q * L) ≤ q * ((sumV L : ℝ) / 2 ^ L) := by
  have hP : (0 : ℝ) < 2 ^ (q * L) := by positivity
  rw [div_le_iff₀ hP, sumV_eq]
  calc ∑ x ∈ range (2 ^ (q * L)), (V (q * L) x : ℝ)
      ≤ ∑ x ∈ range (2 ^ (q * L)), (blockCost L q x : ℝ) :=
        sum_le_sum fun x _ => by exact_mod_cast V_le_blockCost L q x
    _ = _ := by rw [sum_blockCost]; ring

/-- `A_{N+r} ≤ A_N + r`. -/
theorem A_add_le (N r : ℕ) :
    (sumV (N + r) : ℝ) / 2 ^ (N + r) ≤ (sumV N : ℝ) / 2 ^ N + r := by
  have hP : (0 : ℝ) < 2 ^ (N + r) := by positivity
  have hper : ∑ x ∈ range (2 ^ (N + r)), (V N x : ℝ) = 2 ^ r * sumV N := by
    rw [pow_add, sum_range_mul_split, sumV_eq]
    simp only [V_add_pow_mul, sum_const, card_range, nsmul_eq_mul]
    push_cast; ring
  rw [div_le_iff₀ hP, sumV_eq]
  calc ∑ x ∈ range (2 ^ (N + r)), (V (N + r) x : ℝ)
      ≤ ∑ x ∈ range (2 ^ (N + r)), ((V N x : ℝ) + r) :=
        sum_le_sum fun x _ => by exact_mod_cast V_add_le_add N r x
    _ = 2 ^ r * sumV N + 2 ^ (N + r) * r := by
        rw [sum_add_distrib, hper, sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ = _ := by rw [pow_add]; field_simp

/-! ## The crux and the spine reduction (`notes/37`) -/

/-- **The crux (open).**  The adjacent cross-energy of `μ_p` is bounded uniformly in depth.

Equivalently the difference law of two independent `μ_p` points (an iid self-similar law with
digits `e = D − D'` and the inverse branches `y ↦ (3y − e)/2`) has bounded dyadic density at
the point `1`.  Its exact recursion (notes/37 §3) runs over integer shifts `δ`, starting from
`δ = 1`: `λ_n(δ) = 2 ∑_{e ≡ δ (2)} π(e) λ_{n−1}((3δ − e)/2)`, `π = p ∗ p̃`.  The integers visited
never return to `0`, and `|δ|` never decreases.

Evidence [computed, `tools/sandbox/haar_digit_rate/cross_energy_p.c`, sparse forward recursion]:
`crossEnergy` at Fornet's candidate `(18,6,1)/25` is `0.5507, 0.5401, 0.5504, 0.5475, 0.5463`
at `N = 16, 24, 32, 40, 46`.  For the tilted laws `p ∝ (1, e^{−θ}, e^{−2θ})` the values are flat
in `N ≤ 48` at every `θ` tested: `0.811` (θ=0.5), `0.606` (1.0), `0.466` (1.24), `0.430` (1.3),
`0.414` (θ* = 1.326), `0.311` (1.5), `0.083` (2.0).  Meanwhile the diagonal `∫ ρ_N²` grows
like `1.19^N` at `θ = 1.3`, so the bound is genuinely beyond `L²`.
Control (known-false sibling): for the multiplier `1` in place of `3`, i.e. the step
`x ↦ (x + d)/2` with uniform `p` (singular `μ`, entropy `log 3 > log 2`), the same recursion closes
on `δ ∈ {−1,0,1}`.  Its transfer matrix `[[2/3, 4/9], [4/9, 4/9]]` has spectral radius
`(10 + √68)/18 ≈ 1.0137 > 1`, so the cross-energy diverges there, as the reduction requires.
Confidence that `CrossEnergyBounded candidate` holds: ~75%. -/
def CrossEnergyBounded (p : ℕ → ℝ) : Prop := ∃ C : ℝ, ∀ N, crossEnergy p N ≤ C

/-- **Spine moment bound** (notes/37 Theorem A, finite form):
`E_μ[ρ_N^s] ≤ q^N + r ∑_{j<N} q^j (cross-energy at depth N−1−j)^s`.  This is the spine
decomposition of `ρ_N(X)`, `X ∼ μ_p`, unrolled one digit at a time: it is `moment_succ_le`
iterated from `moment p s 0 = 1`. -/
theorem moment_bound (p : ℕ → ℝ) (hp : IsDigitLaw p) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (N : ℕ) :
    moment p s N ≤ spineRatio p s ^ N + siblingWeight p s *
      ∑ j ∈ range N, spineRatio p s ^ j * crossEnergy p (N - 1 - j) ^ s := by
  have hq0 : 0 ≤ spineRatio p s := by
    have := hp.1 0; have := hp.1 1; have := hp.1 2
    unfold spineRatio; positivity
  have hr0 : 0 ≤ siblingWeight p s := by
    have := hp.1 0; have := hp.1 2
    unfold siblingWeight; positivity
  induction N with
  | zero =>
    simp only [pow_zero, range_zero, sum_empty, mul_zero, add_zero, moment, haarAvg, rho]
    simp [Z]
  | succ N ih =>
    refine (moment_succ_le p hp s hs0 hs1 N).trans ?_
    rw [sum_range_succ', pow_succ', add_tsub_cancel_right, Nat.sub_zero, pow_zero, one_mul]
    have hsplit : ∑ j ∈ range N, spineRatio p s ^ (j + 1) * crossEnergy p (N - (j + 1)) ^ s
        = spineRatio p s * ∑ j ∈ range N, spineRatio p s ^ j * crossEnergy p (N - 1 - j) ^ s := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by
        rw [show N - (j + 1) = N - 1 - j by omega, pow_succ']; ring
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left ih hq0]

/-- **Headline reduction** (notes/37 Theorem B, finite form).  If the spine ratio is below `1` at
some `s ∈ (0,1]` (entropy above `log 2`) and the cross-energy is bounded, then the Haar-mean
optimal cost satisfies `∑_{x<2^N} V N x ≤ (p₁ + 2p₂ + ε) N 2^N` for all large `N`, i.e.
`a_* ≤ p₁ + 2p₂`.

Proof route: `moment_bound` gives a uniform `L^{1+s}` bound; Hölder turns the spine law of large
numbers (`V_N ≤ S_N`, the spine cost) into `m{V_N ≤ (c+ε)N} ≥ κ > 0`; block commitment with
Haar-uniform restarts (OE2/AC1) plus Chebyshev makes `V_N/N` concentrate at `a_*` from above,
which forces `a_* ≤ c + ε`.  Confidence ~85% (paper proof in notes/37 §4). -/
theorem haarRate_le_of_crossEnergyBounded (p : ℕ → ℝ) (hp : IsDigitLaw p) (s : ℝ) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hq : spineRatio p s < 1) (hC : CrossEnergyBounded p) :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, (sumV N : ℝ) ≤ (p 1 + 2 * p 2 + ε) * N * 2 ^ N := by
  sorry

/-- The spine ratio of the candidate is below `1` at `s = 1/32` (entropy `0.7078 > log 2`;
numerically `q(1/32) ≈ 0.99978`); proved from rational upper bounds on the four 32nd roots. -/
theorem candidate_spineRatio_lt_one : spineRatio candidate (1 / 32) < 1 := by
  -- `x^{1/32} ≤ u` whenever `x ≤ u^32`
  have key : ∀ x u : ℝ, 0 ≤ x → 0 ≤ u → x ≤ u ^ 32 → x ^ (1 / 32 : ℝ) ≤ u := by
    intro x u hx hu h
    calc x ^ (1 / 32 : ℝ) ≤ (u ^ 32) ^ (1 / 32 : ℝ) := Real.rpow_le_rpow hx h (by norm_num)
      _ = u := by
        rw [show (1 / 32 : ℝ) = ((32 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast hu (by norm_num)
  have h2 := key 2 (510949 / 500000) (by norm_num) (by norm_num) (by norm_num)
  have h0 := key (18 / 25) (989787 / 1000000) (by norm_num) (by norm_num) (by norm_num)
  have h1 := key (6 / 25) (956383 / 1000000) (by norm_num) (by norm_num) (by norm_num)
  have h3 := key (1 / 25) (56519 / 62500) (by norm_num) (by norm_num) (by norm_num)
  have e : ∀ x : ℝ, 0 ≤ x → x ^ (1 + 1 / 32 : ℝ) = x * x ^ (1 / 32 : ℝ) :=
    fun x hx => rpow_one_add_eq hx (by norm_num)
  simp only [spineRatio, candidate]
  rw [e _ (by norm_num), e _ (by norm_num), e _ (by norm_num)]
  have n2 : (0 : ℝ) ≤ 2 ^ (1 / 32 : ℝ) := by positivity
  have n0 : (0 : ℝ) ≤ (18 / 25 : ℝ) ^ (1 / 32 : ℝ) := by positivity
  have n1 : (0 : ℝ) ≤ (6 / 25 : ℝ) ^ (1 / 32 : ℝ) := by positivity
  have n3 : (0 : ℝ) ≤ (1 / 25 : ℝ) ^ (1 / 32 : ℝ) := by positivity
  calc (2 : ℝ) ^ (1 / 32 : ℝ) * (18 / 25 * (18 / 25 : ℝ) ^ (1 / 32 : ℝ) +
        6 / 25 * (6 / 25 : ℝ) ^ (1 / 32 : ℝ) + 1 / 25 * (1 / 25 : ℝ) ^ (1 / 32 : ℝ))
      ≤ 510949 / 500000 * (18 / 25 * (989787 / 1000000) + 6 / 25 * (956383 / 1000000) +
        1 / 25 * (56519 / 62500)) := by gcongr
    _ < 1 := by norm_num

/-- **Conditional `a_* ≤ 8/25 < 1/3`**: bounded adjacent cross-energy for Fornet's candidate would
refute Fornet's mean inequality `a_* ≥ 1/3`. -/
theorem haarRate_le_eight_twentyfifths (hC : CrossEnergyBounded candidate) :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, (sumV N : ℝ) ≤ (8 / 25 + ε) * N * 2 ^ N := by
  intro ε hε
  obtain ⟨N₀, h⟩ := haarRate_le_of_crossEnergyBounded candidate candidate_isDigitLaw (1 / 32)
    (by norm_num) (by norm_num) candidate_spineRatio_lt_one hC ε hε
  exact ⟨N₀, fun N hN => by simpa [candidate_cost] using h N hN⟩

/-! ## Finite Paley–Zygmund -/

/-- Finite Paley–Zygmund: for `f ≥ 0` on a finset and `θ ∈ [0,1]`, the set where `f` exceeds `θ`
times its sum over `s.card` satisfies `(1-θ)² (∑ f)² ≤ #{f > θ·mean} · ∑ f²`. -/
theorem paley_zygmund {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∑ x ∈ s, f x) ^ 2 ≤
      ((s.filter (fun x => θ * (∑ y ∈ s, f y) / s.card < f x)).card : ℝ) *
        ∑ x ∈ s, f x ^ 2 := by
  set S := ∑ y ∈ s, f y
  set A := s.filter (fun x => θ * S / s.card < f x)
  have hS : 0 ≤ S := sum_nonneg hf
  -- the small part contributes at most `θ S`
  have hsmall : ∑ x ∈ s.filter (fun x => ¬ θ * S / s.card < f x), f x ≤ θ * S := by
    rcases Nat.eq_zero_or_pos s.card with hc | hc
    · rw [Finset.card_eq_zero.mp hc]; simp; positivity
    calc ∑ x ∈ s.filter (fun x => ¬ θ * S / s.card < f x), f x
        ≤ ∑ x ∈ s.filter (fun x => ¬ θ * S / s.card < f x), θ * S / s.card :=
          sum_le_sum fun x hx => le_of_not_gt (mem_filter.mp hx).2
      _ ≤ ∑ x ∈ s, θ * S / s.card :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ = θ * S := by
          rw [sum_const, nsmul_eq_mul]; field_simp
  have hsplit : S = ∑ x ∈ A, f x + ∑ x ∈ s.filter (fun x => ¬ θ * S / s.card < f x), f x :=
    (sum_filter_add_sum_filter_not s _ f).symm
  have hbig : (1 - θ) * S ≤ ∑ x ∈ A, f x := by linarith
  have hcs : (∑ x ∈ A, f x) ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, f x ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hA2 : ∑ x ∈ A, f x ^ 2 ≤ ∑ x ∈ s, f x ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have h1 : 0 ≤ (1 - θ) * S := mul_nonneg (by linarith) hS
  calc (1 - θ) ^ 2 * S ^ 2 = ((1 - θ) * S) ^ 2 := by ring
    _ ≤ (∑ x ∈ A, f x) ^ 2 := pow_le_pow_left₀ h1 hbig 2
    _ ≤ (A.card : ℝ) * ∑ x ∈ A, f x ^ 2 := hcs
    _ ≤ (A.card : ℝ) * ∑ x ∈ s, f x ^ 2 := mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _)

end Collatz.Antihydra.HaarDigitRate
