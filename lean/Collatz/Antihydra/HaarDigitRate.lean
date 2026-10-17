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

/-- **Spine moment bound** (notes/37 Theorem A, finite form).  Decompose `ρ_N(X)` along the
spine word of `X ∼ μ_p`: siblings branch off at even states, where the other even digit leads to
the spine's next state `± 1`, and the spine tail beyond step `j` is independent of the first
`j + 1` digits.  Subadditivity of `x ↦ x^s` and Jensen for the sibling subtrees give
`E_μ[ρ_N^s] ≤ q^N + r ∑_{j<N} q^j (cross-energy at depth N−1−j)^s`.

Confidence ~90% (English proof in notes/37 §2; each step is a finite-sum identity or inequality). -/
theorem moment_bound (p : ℕ → ℝ) (hp : IsDigitLaw p) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (N : ℕ) :
    moment p s N ≤ spineRatio p s ^ N + siblingWeight p s *
      ∑ j ∈ range N, spineRatio p s ^ j * crossEnergy p (N - 1 - j) ^ s := by
  sorry

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
numerically `q(1/32) ≈ 0.99978`).  Confidence ~99% (a numeric `rpow` bound, not yet checked in
Lean). -/
theorem candidate_spineRatio_lt_one : spineRatio candidate (1 / 32) < 1 := by
  sorry

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
