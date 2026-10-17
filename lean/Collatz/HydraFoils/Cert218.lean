/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.HydraFoils.Cert218ChunkA
import Collatz.HydraFoils.Cert218ChunkB
import Collatz.HydraFoils.Cert218ChunkC

/-!
# #218 drains at defect 1: a ten-digit lookahead certificate

The window condition fails for #218 at defect `1` (`hydra218_window`): with only `x mod 3` and an
adversarial next digit, the adversary always offers the residues `{0, 1}` (walk `+3, +1`).  But
the low `k` base-3 digits of the image depend only on the low `k + 1` digits of `x`, so a steering
may look ahead.  On `x mod 3^10` the energy game is won: a potential `φ ≤ 135` on `x mod 3^10`
with, at every `x mod 3^11`, a choice `c ∈ {0, 1}` along which `14 w + φ` falls by one (mean walk
`≤ -1/14` per step).  `phi` packs `φ` into a balanced tree of 32-entry leaves; `chk` is checked on
all `3^11 = 177147` residues by `decide +kernel` in chunks.  The certificate was found by value
iteration (`sim/hydra_foils/energy.js`) and re-checked independently in Python.

**Result** (`hydra218_halting_dense_one`): halting members are dense in `F_{L,1}` for #218, so
`d_min = 2` from the window condition is not sharp.
-/

namespace Collatz.HydraFoils.Cert218

theorem chk_all (u : ℕ) (hu : u < 177147) : chk u = true := by
  by_cases h0 : u < 10000
  · exact of_chunk chunk0 u (by omega) h0
  by_cases h1 : u < 20000
  · exact of_chunk chunk1 u (by omega) h1
  by_cases h2 : u < 30000
  · exact of_chunk chunk2 u (by omega) h2
  by_cases h3 : u < 40000
  · exact of_chunk chunk3 u (by omega) h3
  by_cases h4 : u < 50000
  · exact of_chunk chunk4 u (by omega) h4
  by_cases h5 : u < 60000
  · exact of_chunk chunk5 u (by omega) h5
  by_cases h6 : u < 70000
  · exact of_chunk chunk6 u (by omega) h6
  by_cases h7 : u < 80000
  · exact of_chunk chunk7 u (by omega) h7
  by_cases h8 : u < 90000
  · exact of_chunk chunk8 u (by omega) h8
  by_cases h9 : u < 100000
  · exact of_chunk chunk9 u (by omega) h9
  by_cases h10 : u < 110000
  · exact of_chunk chunk10 u (by omega) h10
  by_cases h11 : u < 120000
  · exact of_chunk chunk11 u (by omega) h11
  by_cases h12 : u < 130000
  · exact of_chunk chunk12 u (by omega) h12
  by_cases h13 : u < 140000
  · exact of_chunk chunk13 u (by omega) h13
  by_cases h14 : u < 150000
  · exact of_chunk chunk14 u (by omega) h14
  by_cases h15 : u < 160000
  · exact of_chunk chunk15 u (by omega) h15
  by_cases h16 : u < 170000
  · exact of_chunk chunk16 u (by omega) h16
  exact of_chunk chunk17 u (by omega) (by omega)

theorem img_nat (u c : ℕ) : ((hydra218Sys.img u + c) % 59049).toNat = nxt u c := by
  have h3 : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
  rw [nxt_eq]
  unfold Sys.img Sys.res
  change ((4 * ((u : ℤ) / 3) + [1, 2, 3].getD ((u : ℤ) % 3).toNat 0 + c) % 59049).toNat = _
  rcases h3 with h | h | h
  · have hz : (u : ℤ) % 3 = 0 := by omega
    rw [hz]; simp only [Int.toNat_zero, List.getD_cons_zero]; omega
  · have hz : (u : ℤ) % 3 = 1 := by omega
    rw [hz]; simp only [Int.toNat_one, List.getD_cons_succ, List.getD_cons_zero]; omega
  · have hz : (u : ℤ) % 3 = 2 := by omega
    rw [hz]
    simp only [show (2 : ℤ).toNat = 1 + 1 from rfl, List.getD_cons_succ, List.getD_cons_zero]
    omega

theorem w_nat (u : ℕ) : hydra218Sys.w.getD (u % 3) 0 = (wP (u % 3) : ℤ) - wM (u % 3) := by
  have h3 : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] <;> rfl

theorem ok_sound (u c : ℕ) (h : ok u c = true) :
    ((14 : ℕ) : ℤ) * hydra218Sys.w.getD (u % 3) 0 + (phi (nxt u c) : ℤ) + 1 ≤ phi (u % 59049) := by
  rw [ok_eq] at h
  have := Nat.le_of_ble_eq_true h
  rw [w_nat]; push_cast; omega

/-- The certificate, in the form `Sys.halting_dense_of_modCert` takes. -/
theorem cert (u : ℕ) (hu : u < hydra218Sys.q * 59049) :
    ∃ c : ℕ, c ≤ 1 ∧ ((14 : ℕ) : ℤ) * hydra218Sys.w.getD (u % hydra218Sys.q) 0 +
      (phi (((hydra218Sys.img u + (c : ℤ)) % ((59049 : ℕ) : ℤ)).toNat) : ℤ) + 1 ≤
        phi (u % 59049) := by
  have hu' : u < 177147 := hu
  have hq : hydra218Sys.q = 3 := rfl
  have hQ : ((59049 : ℕ) : ℤ) = 59049 := rfl
  rw [hq, hQ]
  have h := chk_all u hu'
  simp only [chk, Bool.or_eq_true] at h
  rcases h with h | h
  · refine ⟨0, by omega, ?_⟩
    have e := img_nat u 0
    simp only [Nat.cast_zero] at e ⊢
    rw [e]; exact ok_sound u 0 h
  · refine ⟨1, le_rfl, ?_⟩
    have e := img_nat u 1
    simp only [Nat.cast_one] at e ⊢
    rw [e]; exact ok_sound u 1 h

/-- **T3, target 4 (#218).**  Halting members are dense in `F_{L,1}` for #218: every member
agrees on all blocks `< K` with a member that halts from `(1, 3)`.  So the window bound
`d_min = 2` (`hydra218_window`) is not sharp. -/
theorem hydra218_halting_dense_one {L : ℕ} (hL : 1 ≤ L) (σ₀ : ℤ → Fin 2) (K : ℤ) :
    ∃ σ : ℤ → Fin 2, (∀ b < K, σ b = σ₀ b) ∧ hydra218Sys.Halts (member 3 L σ) (1, 3) :=
  hydra218Sys.halting_dense_of_modCert (Q := 59049) (by decide) (by decide) hL (by norm_num) phi 14
    cert σ₀ K (1, 3) hydra218_esc

end Collatz.HydraFoils.Cert218
