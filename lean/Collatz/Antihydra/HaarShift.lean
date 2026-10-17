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

end Collatz.Antihydra.HaarDigitRate
