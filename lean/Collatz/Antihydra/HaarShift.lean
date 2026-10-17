/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.Antihydra.HaarDigitRate

/-!
# The integer shift recursion for the cross-energy (notes/37 §3, form 2)

`crossShift p N δ = ∫ ρ_N(y) ρ_N(y + δ) dm(y)` is the depth-`N` dyadic density of the
difference law `X' − X` at the point `δ`.  It obeys an explicit recursion on the positive
integers, with the pair law `π(0) = ∑ p_d²`, `π(1) = p₁(p₀ + p₂)`, `π(2) = p₀p₂`:

* `C_{N+1}(2u+1) = 2π(1)·(C_N(3u+1) + C_N(3u+2))`;
* `C_{N+1}(2u+2) = 2π(0)·C_N(3u+3) + 2π(2)·(C_N(3u+2) + C_N(3u+4))`;
* `C_0 ≡ 1`.

So the crux `CrossEnergyBounded p` (the `δ = 1` case) is a statement about an explicit
nonnegative kernel on `ℕ_{≥1}`: `crossEnergy p N = shiftKernel p N 1` (`crossEnergy_eq_kernel`),
where `shiftKernel` is defined by the recursion alone, with no reference to residues.
-/

namespace Collatz.Antihydra.HaarDigitRate

open Finset

/-- Shifted cross-energy `C_N(δ) = ∫ ρ_N(y) ρ_N(y + δ) dm(y) = 2^N P(X' − X ≡ δ mod 2^N)`. -/
noncomputable def crossShift (p : ℕ → ℝ) (N δ : ℕ) : ℝ :=
  haarAvg N (fun r => rho p N r * rho p N (r + δ))

theorem crossEnergy_eq_crossShift (p : ℕ → ℝ) (N : ℕ) : crossEnergy p N = crossShift p N 1 :=
  rfl

/-- The pair law `π = p ∗ p̃` on `|e| ∈ {0,1,2}` (one side): `π(0) = ∑ p_d²`,
`π(1) = p₁(p₀ + p₂)`, `π(2) = p₀p₂`. -/
noncomputable def pairLaw (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2
  | 1 => p 1 * (p 0 + p 2)
  | 2 => p 0 * p 2
  | _ => 0

theorem crossShift_zero (p : ℕ → ℝ) (δ : ℕ) : crossShift p 0 δ = 1 := by
  simp [crossShift, haarAvg, rho, Z]

/-- Reindexing one affine cross term: `∑_{m < 2^N} ρ(3m+c) ρ(3m+c+s) = 2^N C_N(s)`. -/
theorem sum_rho_affine (p : ℕ → ℝ) (N c s : ℕ) :
    ∑ m ∈ range (2 ^ N), rho p N (3 * m + c) * rho p N (3 * m + c + s) =
      2 ^ N * crossShift p N s := by
  have hper : ∀ x k, rho p N (x + 2 ^ N * k) * rho p N (x + 2 ^ N * k + s) =
      rho p N x * rho p N (x + s) := by
    intro x k
    rw [show x + 2 ^ N * k + s = (x + s) + 2 ^ N * k by ring, rho_add_pow_mul, rho_add_pow_mul]
  have e := sum_range_pow_affine N 3 c rfl (fun x => rho p N x * rho p N (x + s)) hper
  rw [e, crossShift, haarAvg]
  field_simp

theorem sum_rho_affine_zero (p : ℕ → ℝ) (N s : ℕ) :
    ∑ m ∈ range (2 ^ N), rho p N (3 * m) * rho p N (3 * m + s) = 2 ^ N * crossShift p N s := by
  simpa using sum_rho_affine p N 0 s

/-- Odd shifts: `C_{N+1}(2u+1) = 2π(1)(C_N(3u+1) + C_N(3u+2))`. -/
theorem crossShift_succ_odd (p : ℕ → ℝ) (N u : ℕ) :
    crossShift p (N + 1) (2 * u + 1) =
      2 * pairLaw p 1 * (crossShift p N (3 * u + 1) + crossShift p N (3 * u + 2)) := by
  have hpt : ∀ m, rho p (N + 1) (2 * m) * rho p (N + 1) (2 * m + (2 * u + 1)) +
      rho p (N + 1) (2 * m + 1) * rho p (N + 1) (2 * m + 1 + (2 * u + 1)) =
      4 * p 0 * p 1 * (rho p N (3 * m) * rho p N (3 * m + (3 * u + 2))) +
      4 * p 2 * p 1 * (rho p N (3 * m + 1) * rho p N (3 * m + 1 + (3 * u + 1))) +
      4 * p 1 * p 0 * (rho p N (3 * m + 2) * rho p N (3 * m + 2 + (3 * u + 1))) +
      4 * p 1 * p 2 * (rho p N (3 * m + 2) * rho p N (3 * m + 2 + (3 * u + 2))) := by
    intro m
    rw [show 2 * m + (2 * u + 1) = 2 * (m + u) + 1 by ring,
      show 2 * m + 1 + (2 * u + 1) = 2 * (m + u + 1) by ring]
    simp only [rho_succ_even, rho_succ_odd]
    rw [show 3 * (m + u) + 2 = 3 * m + (3 * u + 2) by ring,
      show 3 * (m + u + 1) + 1 = 3 * m + 2 + (3 * u + 2) by ring,
      show 3 * (m + u + 1) = 3 * m + 2 + (3 * u + 1) by ring,
      show 3 * m + 1 + (3 * u + 1) = 3 * m + (3 * u + 2) by ring]
    ring
  rw [crossShift, haarAvg, pow_succ', sum_range_two_mul]
  simp only [hpt, sum_add_distrib, ← mul_sum, sum_rho_affine, sum_rho_affine_zero]
  rw [pairLaw]
  field_simp
  ring

/-- Even shifts: `C_{N+1}(2u+2) = 2π(0) C_N(3u+3) + 2π(2)(C_N(3u+2) + C_N(3u+4))`. -/
theorem crossShift_succ_even (p : ℕ → ℝ) (N u : ℕ) :
    crossShift p (N + 1) (2 * u + 2) =
      2 * pairLaw p 0 * crossShift p N (3 * u + 3) +
        2 * pairLaw p 2 * (crossShift p N (3 * u + 2) + crossShift p N (3 * u + 4)) := by
  have hpt : ∀ m, rho p (N + 1) (2 * m) * rho p (N + 1) (2 * m + (2 * u + 2)) +
      rho p (N + 1) (2 * m + 1) * rho p (N + 1) (2 * m + 1 + (2 * u + 2)) =
      4 * p 0 * p 0 * (rho p N (3 * m) * rho p N (3 * m + (3 * u + 3))) +
      4 * p 0 * p 2 * (rho p N (3 * m) * rho p N (3 * m + (3 * u + 4))) +
      4 * p 2 * p 0 * (rho p N (3 * m + 1) * rho p N (3 * m + 1 + (3 * u + 2))) +
      4 * p 2 * p 2 * (rho p N (3 * m + 1) * rho p N (3 * m + 1 + (3 * u + 3))) +
      4 * p 1 * p 1 * (rho p N (3 * m + 2) * rho p N (3 * m + 2 + (3 * u + 3))) := by
    intro m
    rw [show 2 * m + (2 * u + 2) = 2 * (m + u + 1) by ring,
      show 2 * m + 1 + (2 * u + 2) = 2 * (m + u + 1) + 1 by ring]
    simp only [rho_succ_even, rho_succ_odd]
    rw [show 3 * (m + u + 1) + 2 = 3 * m + 2 + (3 * u + 3) by ring,
      show 3 * (m + u + 1) + 1 = 3 * m + (3 * u + 4) by ring,
      show 3 * (m + u + 1) = 3 * m + (3 * u + 3) by ring,
      show 3 * m + 1 + (3 * u + 2) = 3 * m + (3 * u + 3) by ring,
      show 3 * m + 1 + (3 * u + 3) = 3 * m + (3 * u + 4) by ring]
    ring
  rw [crossShift, haarAvg, pow_succ', sum_range_two_mul]
  simp only [hpt, sum_add_distrib, ← mul_sum, sum_rho_affine, sum_rho_affine_zero]
  rw [pairLaw, pairLaw]
  field_simp
  ring

/-- The diagonal: `C_{N+1}(0) = 2π(0) C_N(0) + 4π(2) C_N(1)` (so `∫ ρ²` is fed by the
cross-energy). -/
theorem crossShift_succ_zero (p : ℕ → ℝ) (N : ℕ) :
    crossShift p (N + 1) 0 =
      2 * pairLaw p 0 * crossShift p N 0 + 4 * pairLaw p 2 * crossShift p N 1 := by
  have hpt : ∀ m, rho p (N + 1) (2 * m) * rho p (N + 1) (2 * m + 0) +
      rho p (N + 1) (2 * m + 1) * rho p (N + 1) (2 * m + 1 + 0) =
      4 * p 0 * p 0 * (rho p N (3 * m) * rho p N (3 * m + 0)) +
      8 * p 0 * p 2 * (rho p N (3 * m) * rho p N (3 * m + 1)) +
      4 * p 2 * p 2 * (rho p N (3 * m + 1) * rho p N (3 * m + 1 + 0)) +
      4 * p 1 * p 1 * (rho p N (3 * m + 2) * rho p N (3 * m + 2 + 0)) := by
    intro m
    simp only [add_zero, rho_succ_even, rho_succ_odd]
    ring
  rw [crossShift, haarAvg, pow_succ', sum_range_two_mul]
  simp only [hpt, sum_add_distrib, ← mul_sum, sum_rho_affine, sum_rho_affine_zero]
  rw [pairLaw, pairLaw]
  field_simp
  ring

/-- **The shift kernel**: the recursion of `crossShift`, stated with no reference to residues.
`K_0 ≡ 1`; odd `δ = 2u+1` feeds `3u+1, 3u+2`; even `δ = 2u ≥ 2` feeds `3u−1, 3u, 3u+1`; and
`δ = 0` feeds `0, 1`. -/
noncomputable def shiftKernel (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | N + 1, δ =>
    if δ % 2 = 1 then
      2 * pairLaw p 1 * (shiftKernel p N (3 * (δ / 2) + 1) + shiftKernel p N (3 * (δ / 2) + 2))
    else if δ = 0 then
      2 * pairLaw p 0 * shiftKernel p N 0 + 4 * pairLaw p 2 * shiftKernel p N 1
    else
      2 * pairLaw p 0 * shiftKernel p N (3 * (δ / 2)) +
        2 * pairLaw p 2 * (shiftKernel p N (3 * (δ / 2) - 1) + shiftKernel p N (3 * (δ / 2) + 1))

/-- The residue-free form of the shifted cross-energies. -/
theorem crossShift_eq_shiftKernel (p : ℕ → ℝ) : ∀ N δ, crossShift p N δ = shiftKernel p N δ := by
  intro N
  induction N with
  | zero => intro δ; rw [crossShift_zero, shiftKernel]
  | succ N ih =>
    intro δ
    obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' δ
    · rcases u with _ | u
      · rw [crossShift_succ_zero, shiftKernel, ih, ih]; simp
      · have h1 : 2 * (u + 1) % 2 = 0 := by omega
        have h2 : 2 * (u + 1) / 2 = u + 1 := by omega
        rw [show 2 * (u + 1) = 2 * u + 2 by ring] at h1 h2 ⊢
        rw [crossShift_succ_even, shiftKernel, if_neg (by omega), if_neg (by omega), h2, ih, ih,
          ih, show 3 * (u + 1) = 3 * u + 3 by ring, show 3 * u + 3 - 1 = 3 * u + 2 by omega,
          show 3 * u + 3 + 1 = 3 * u + 4 by ring]
    · have h2 : (2 * u + 1) / 2 = u := by omega
      rw [crossShift_succ_odd, shiftKernel, if_pos (by omega), h2, ih, ih]

/-- **The crux as an integer recursion**: the adjacent cross-energy is the shift kernel at `1`. -/
theorem crossEnergy_eq_shiftKernel (p : ℕ → ℝ) (N : ℕ) :
    crossEnergy p N = shiftKernel p N 1 :=
  crossShift_eq_shiftKernel p N 1

theorem crossEnergyBounded_iff_shiftKernel (p : ℕ → ℝ) :
    CrossEnergyBounded p ↔ ∃ C : ℝ, ∀ N, shiftKernel p N 1 ≤ C := by
  simp only [CrossEnergyBounded, crossEnergy_eq_shiftKernel]

/-- Anchor: `Λ_1 = 4π(1) = 456/625` for the candidate, by the kernel. -/
theorem crossEnergy_candidate_one : crossEnergy candidate 1 = 456 / 625 := by
  rw [crossEnergy_eq_shiftKernel]
  simp [shiftKernel, pairLaw, candidate]
  norm_num

/-! ## The kernel as an operator, and the parity form of the crux

`kernelOp p` is the one-step operator `𝒦` of the shift kernel acting on arbitrary test functions,
so `shiftKernel p N = 𝒦^N 1`.  Since `𝒦 1 = 1 + β χ` with `χ(δ) = (−1)^δ` and
`β = (p₀ − p₁ + p₂)²`, the cross-energy increments are the weighted parity correlations
`P_n = (𝒦^n χ)(1)` (`crossEnergy_succ`, `crossEnergy_eq_one_add_sum`).  So the crux is exactly a
bound on the partial sums of `P_n` (`crossEnergyBounded_iff_parity`).  The odd parents cancel
exactly in `𝒦 χ` (`kernelOp_parity`), which is why `P_n` carries a 4-adic character. -/

/-- The one-step operator of the shift kernel on a test function `g : ℕ → ℝ`. -/
noncomputable def kernelOp (p : ℕ → ℝ) (g : ℕ → ℝ) (δ : ℕ) : ℝ :=
  if δ % 2 = 1 then 2 * pairLaw p 1 * (g (3 * (δ / 2) + 1) + g (3 * (δ / 2) + 2))
  else if δ = 0 then 2 * pairLaw p 0 * g 0 + 4 * pairLaw p 2 * g 1
  else 2 * pairLaw p 0 * g (3 * (δ / 2)) +
    2 * pairLaw p 2 * (g (3 * (δ / 2) - 1) + g (3 * (δ / 2) + 1))

theorem shiftKernel_succ (p : ℕ → ℝ) (N : ℕ) :
    shiftKernel p (N + 1) = kernelOp p (shiftKernel p N) := by
  funext δ; simp only [shiftKernel, kernelOp]

theorem shiftKernel_eq_iterate (p : ℕ → ℝ) (N : ℕ) :
    shiftKernel p N = (kernelOp p)^[N] (fun _ => 1) := by
  induction N with
  | zero => funext δ; simp [shiftKernel]
  | succ N ih => rw [shiftKernel_succ, ih, Function.iterate_succ_apply']

theorem kernelOp_linear (p : ℕ → ℝ) (a b : ℝ) (f g : ℕ → ℝ) :
    kernelOp p (fun δ => a * f δ + b * g δ) = fun δ => a * kernelOp p f δ + b * kernelOp p g δ := by
  funext δ; simp only [kernelOp]; split_ifs <;> ring

theorem iterate_kernelOp_linear (p : ℕ → ℝ) (a b : ℝ) (n : ℕ) : ∀ f g : ℕ → ℝ,
    (kernelOp p)^[n] (fun δ => a * f δ + b * g δ) =
      fun δ => a * (kernelOp p)^[n] f δ + b * (kernelOp p)^[n] g δ := by
  induction n with
  | zero => intro f g; rfl
  | succ n ih =>
    intro f g
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      kernelOp_linear, ih]

/-- The parity character `χ(δ) = (−1)^δ`. -/
noncomputable def parityChar (δ : ℕ) : ℝ := (-1) ^ δ

/-- The weighted parity correlation `P_n = (𝒦^n χ)(1) = ∑_δ m_n(δ)(−1)^δ` of the forward shift
measure `m_n` from `δ = 1`. -/
noncomputable def parityCorr (p : ℕ → ℝ) (n : ℕ) : ℝ := (kernelOp p)^[n] parityChar 1

/-- The parity bias `β = (p₀ − p₁ + p₂)² = (2π(0) + 4π(2) − 4π(1))/2`. -/
noncomputable def parityBias (p : ℕ → ℝ) : ℝ := (p 0 - p 1 + p 2) ^ 2

theorem parityChar_of_odd (δ : ℕ) (h : δ % 2 = 1) : parityChar δ = -1 := by
  rw [parityChar, neg_one_pow_eq_pow_mod_two, h, pow_one]

theorem parityChar_of_even (δ : ℕ) (h : δ % 2 = 0) : parityChar δ = 1 := by
  rw [parityChar, neg_one_pow_eq_pow_mod_two, h, pow_zero]

/-- `𝒦 1 = 1 + β χ` for a digit law. -/
theorem kernelOp_one (p : ℕ → ℝ) (hp : IsDigitLaw p) :
    kernelOp p (fun _ => 1) = fun δ => 1 * 1 + parityBias p * parityChar δ := by
  have h := hp.2
  funext δ
  simp only [kernelOp, parityBias, pairLaw]
  split_ifs with h1 h0
  · rw [parityChar_of_odd δ h1]
    linear_combination (p 0 + p 1 + p 2 + 1) * h
  · rw [parityChar_of_even δ (by omega)]
    linear_combination (p 0 + p 1 + p 2 + 1) * h
  · rw [parityChar_of_even δ (by omega)]
    linear_combination (p 0 + p 1 + p 2 + 1) * h

/-- **Increment identity**: `Λ_{n+1} = Λ_n + β P_n`. -/
theorem crossEnergy_succ (p : ℕ → ℝ) (hp : IsDigitLaw p) (n : ℕ) :
    crossEnergy p (n + 1) = crossEnergy p n + parityBias p * parityCorr p n := by
  rw [crossEnergy_eq_shiftKernel, crossEnergy_eq_shiftKernel, shiftKernel_eq_iterate,
    shiftKernel_eq_iterate, Function.iterate_succ_apply, kernelOp_one p hp,
    iterate_kernelOp_linear, parityCorr]
  ring

/-- `Λ_N = 1 + β ∑_{n<N} P_n`. -/
theorem crossEnergy_eq_one_add_sum (p : ℕ → ℝ) (hp : IsDigitLaw p) (N : ℕ) :
    crossEnergy p N = 1 + parityBias p * ∑ n ∈ range N, parityCorr p n := by
  induction N with
  | zero => rw [crossEnergy_eq_shiftKernel]; simp [shiftKernel]
  | succ N ih => rw [crossEnergy_succ p hp, ih, sum_range_succ]; ring

/-- **The crux in parity form**: for a digit law with `p₁ ≠ p₀ + p₂`, the adjacent cross-energy
is bounded iff the partial sums of the weighted parity correlations are bounded above. -/
theorem crossEnergyBounded_iff_parity (p : ℕ → ℝ) (hp : IsDigitLaw p) (hβ : 0 < parityBias p) :
    CrossEnergyBounded p ↔ ∃ C : ℝ, ∀ N, ∑ n ∈ range N, parityCorr p n ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(C - 1) / parityBias p, fun N => ?_⟩
    have := hC N
    rw [crossEnergy_eq_one_add_sum p hp] at this
    rw [le_div_iff₀ hβ]; linarith
  · rintro ⟨C, hC⟩
    refine ⟨1 + parityBias p * C, fun N => ?_⟩
    rw [crossEnergy_eq_one_add_sum p hp]
    have := mul_le_mul_of_nonneg_left (hC N) hβ.le
    linarith

/-- The 4-adic character `χ₄(δ) = 1[δ even]·(−1)^{δ/2}`. -/
noncomputable def char4 (δ : ℕ) : ℝ := if δ % 2 = 0 then (-1) ^ (δ / 2) else 0

/-- **Parity cancellation**: `𝒦 χ = (2π(0) − 4π(2)) χ₄`.  The two successors of an odd shift are
consecutive integers with equal weights, so odd parents contribute nothing. -/
theorem kernelOp_parity (p : ℕ → ℝ) :
    kernelOp p parityChar = fun δ => (2 * pairLaw p 0 - 4 * pairLaw p 2) * char4 δ := by
  funext δ
  obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' δ
  · rcases u with _ | u
    · simp [kernelOp, char4, parityChar]; ring
    · have h2 : 2 * (u + 1) / 2 = u + 1 := by omega
      simp only [kernelOp, char4, parityChar, h2, if_neg (show ¬ 2 * (u + 1) % 2 = 1 by omega),
        if_neg (show ¬ 2 * (u + 1) = 0 by omega), if_pos (show 2 * (u + 1) % 2 = 0 by omega)]
      rw [show 3 * (u + 1) - 1 = 2 * (u + 1) + u by omega,
        show 3 * (u + 1) = 2 * (u + 1) + (u + 1) by ring,
        show 2 * (u + 1) + (u + 1) + 1 = 2 * (u + 2) + u by ring]
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
      ring
  · have h2 : (2 * u + 1) / 2 = u := by omega
    simp only [kernelOp, char4, parityChar, h2, if_pos (show (2 * u + 1) % 2 = 1 by omega),
      if_neg (show ¬ (2 * u + 1) % 2 = 0 by omega)]
    rw [show 3 * u + 1 = 2 * u + u + 1 by ring, show 3 * u + 2 = 2 * (u + 1) + u by ring]
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    ring

/-- `P_{n+1} = (2π(0) − 4π(2)) (𝒦^n χ₄)(1)`. -/
theorem parityCorr_succ (p : ℕ → ℝ) (n : ℕ) :
    parityCorr p (n + 1) = (2 * pairLaw p 0 - 4 * pairLaw p 2) * (kernelOp p)^[n] char4 1 := by
  have h := iterate_kernelOp_linear p (2 * pairLaw p 0 - 4 * pairLaw p 2) 0 n char4 char4
  simp only [zero_mul, add_zero] at h
  rw [parityCorr, Function.iterate_succ_apply, kernelOp_parity, h]

theorem candidate_parityBias : parityBias candidate = 169 / 625 := by
  simp only [parityBias, candidate]; norm_num

/-- **Open (sufficient for the crux).**  The weighted parity correlations of the shift chain are
absolutely summable.  It implies `CrossEnergyBounded p` (`crossEnergyBounded_of_paritySummable`),
which needs only bounded partial sums.

Evidence [computed, `tools/sandbox/haar_digit_rate/parity_corr.c`: the forward recursion in
doubles, exact up to rounding].  For the candidate `(18,6,1)/25`, `P_n/Λ_n` is `+8.1e−2`
(n=10), `−1.5e−2` (20), `+1.8e−2` (30), `+2.9e−3` (40), `−4.6e−3` (42).  The decay is slow,
about `e^{−0.07 n}`, and the signs oscillate.  `Λ_n` stays in `[0.534, 0.551]` for `20 ≤ n ≤ 44`.  Control: the multiplier-1 sibling
(`x ↦ (x + d)/2`, uniform `p`) has `Λ_n → ∞`, so its `P_n` are not summable.

Finer scales [computed, `fwd_tv.c`]: the total-variation distance of the forward measure from
uniform mod `2^k` fits `TV_{n,k} ≈ 0.18·exp(−0.10 n + 0.33 k)` on `16 ≤ n ≤ 44`, `k ≤ 20`.  No
mechanism for the decay is known; it is a 2-adic analogue of the finest-scale smoothness of a
self-similar measure with algebraic contraction `2/3` (notes/37 §8–9).  Confidence that it holds
for the candidate: ~65%. -/
def ParityCorrSummable (p : ℕ → ℝ) : Prop := Summable (fun n => |parityCorr p n|)

theorem crossEnergyBounded_of_paritySummable (p : ℕ → ℝ) (hp : IsDigitLaw p)
    (hβ : 0 < parityBias p) (h : ParityCorrSummable p) : CrossEnergyBounded p := by
  rw [crossEnergyBounded_iff_parity p hp hβ]
  refine ⟨∑' n, |parityCorr p n|, fun N => ?_⟩
  calc ∑ n ∈ range N, parityCorr p n ≤ ∑ n ∈ range N, |parityCorr p n| :=
        sum_le_sum fun n _ => le_abs_self _
    _ ≤ ∑' n, |parityCorr p n| := h.sum_le_tsum _ fun n _ => abs_nonneg _

/-- The headline from the parity form: summable parity correlations give `a_* ≤ 8/25`. -/
theorem candidate_crossEnergyBounded_of_paritySummable (h : ParityCorrSummable candidate) :
    CrossEnergyBounded candidate :=
  crossEnergyBounded_of_paritySummable candidate candidate_isDigitLaw
    (by rw [candidate_parityBias]; norm_num) h

end Collatz.Antihydra.HaarDigitRate
