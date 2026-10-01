/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Phase
import Collatz.BMO.Problem9.Cubic

/-!
# BMO #9, port of Rocq `Module Stages` (BMO9.v lines 2471-2558, ccz181078)

`through`: given returning entries at every smaller level, the table reaches `target` with an
entry obeying `CheckTable.Bounded`.  Rocq's hypothesis `0 <= target` is vacuous for `ℕ` and
dropped.  `CheckTable.split2` is on `ℕ` (Rocq: `positive`), so `split2_spec` assumes `0 < n`.
-/

namespace BMO9.Stages

open Table Phase Cubic

theorem split2_spec (n : ℕ) (hn : 0 < n) :
    1 ≤ (CheckTable.split2 n).2 ∧ Odd (CheckTable.split2 n).2 ∧
      n = 2^(CheckTable.split2 n).1 * (CheckTable.split2 n).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [CheckTable.split2]
    split_ifs with h
    · obtain ⟨h1, h2, h3⟩ := ih (n/2) (by omega) (by omega)
      refine ⟨h1, h2, ?_⟩
      simp only [pow_succ]
      calc n = 2*(n/2) := by omega
        _ = _ := by nth_rw 1 [h3]; ring
    · refine ⟨by omega, Nat.odd_iff.2 (by omega), by simp⟩

theorem stage_parameters (l : ℕ) (B e : ℤ) (hl : 16 ≤ l) (hB : Built l (.one B e))
    (ho : Odd B) : ∃ (s : ℕ) (r : ℤ), (1 ≤ s ∧ s < l) ∧ B + 3 = 2^s*r ∧ Odd r ∧
      s ≤ 3*CheckTable.log2up l + 4 := by
  obtain ⟨⟨he, hm⟩, -⟩ := built_valid hB
  have hE := built_cubic _ _ hB
  simp only [steps] at hE
  obtain ⟨hr, hro, hf⟩ := split2_spec (B+3).toNat (by omega)
  set s := (CheckTable.split2 (B+3).toNat).1
  set r := (CheckTable.split2 (B+3).toNat).2
  have hfactor : B + 3 = 2^s*(r:ℤ) := by
    have : ((B+3).toNat : ℤ) = ((2^s*r : ℕ) : ℤ) := congrArg _ hf
    rw [Int.toNat_of_nonneg (by omega)] at this; push_cast at this; exact this
  have hs1 : 1 ≤ s := by
    by_contra hcon
    have h0 : s = 0 := by omega
    rw [h0, pow_zero, one_mul] at hfactor
    obtain ⟨t, ht⟩ := hro; obtain ⟨u, hu⟩ := ho
    omega
  have hP : (0:ℤ) < 2^s := by positivity
  have hbound : (2:ℤ)^s ≤ 12*(l:ℤ)^3+4 := by
    have : (1:ℤ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hlt : (2:ℤ)^s < 2^l := lt_of_le_of_lt hbound (cubic_exp l hl)
  have hsl : s < l := (pow_lt_pow_iff_right₀ (by norm_num)).1 hlt
  refine ⟨s, r, ⟨hs1, hsl⟩, hfactor, by exact_mod_cast hro, ?_⟩
  apply lookup_index l s (by omega) hs1
  have : (0:ℤ) ≤ (l:ℤ)^3 := by positivity
  linarith

theorem next_stage (l : ℕ) (B e : ℤ) (hl : 16 ≤ l) (hB : Built l (.one B e))
    (hsmall : ∀ s, 1 ≤ s → s < l → ∃ g, Built s g ∧ Returns Built s g) :
    ∃ (n : ℕ) (v f : ℤ), 2 ≤ n ∧ Built (l+n) (.one v f) ∧
      span l n ((6*CheckTable.log2up l + 9 : ℕ) : ℤ) := by
  rcases Int.even_or_odd B with he | ho
  · obtain ⟨hend, hspan⟩ := stage_even l B e (by omega) hB he
    exact ⟨2, _, _, le_rfl, hend, span_mono _ _ _ _ (by push_cast; omega) hspan⟩
  · obtain ⟨s, r, hs, hfactor, hr, hbound⟩ := stage_parameters l B e hl hB ho
    obtain ⟨g, hg, hret⟩ := hsmall s hs.1 hs.2
    obtain ⟨n, v, f, hn, hend, hspan⟩ := stage_odd l B e s r g hB hs hfactor hr hg hret
    exact ⟨2+n, v, f, by omega, by rwa [← Nat.add_assoc],
      span_mono _ _ _ _ (by push_cast; omega) hspan⟩

/-- Only strictly smaller G-indices are assumed.  In particular the current phase may end
beyond `target`: `span` supplies the needed prefix. -/
theorem through (target : ℕ)
    (hreturns : ∀ s, 1 ≤ s → s < target → ∃ g, Built s g ∧ Returns Built s g) :
    ∃ f, Built target f ∧ CheckTable.Bounded target f := by
  by_cases hbase : target ≤ 16
  · rcases Nat.eq_zero_or_pos target with rfl | hpos
    · exact ⟨.one 1 0, Built.root, by simp [CheckTable.Bounded, steps, CheckTable.depth]⟩
    · obtain ⟨f, hf, hb, -⟩ := CheckTable.base_structured target hpos (by omega)
      exact ⟨f, hf, hb⟩
  · have hgo : ∀ (n l : ℕ) (B e : ℤ), 16 ≤ l → l ≤ target → target - l ≤ n →
        Built l (.one B e) → ∃ f, Built target f ∧ CheckTable.Bounded target f := by
      intro n
      induction n with
      | zero =>
          intro l B e hl hlt hfuel hB
          obtain rfl : target = l := by omega
          exact ⟨_, hB, built_cubic _ _ hB, by simp [CheckTable.depth]⟩
      | succ n ih =>
          intro l B e hl hlt hfuel hB
          obtain ⟨m, v, f, hm, hend, hspan⟩ :=
            next_stage l B e hl hB (fun s hs1 hs2 ↦ hreturns s hs1 (by omega))
          by_cases hstop : target ≤ l + m
          · obtain ⟨g, hg, hd⟩ := hspan (target - l) (by omega)
            rw [show l + (target - l) = target by omega] at hg
            refine ⟨g, hg, built_cubic _ _ hg, ?_⟩
            have := Nat.clog_mono_right 2 hlt
            simp only [CheckTable.log2up] at hd ⊢
            omega
          · exact ih (l+m) v f (by omega) (by omega) (by omega) hend
    exact hgo (target - 16) 16 37 12 le_rfl (by omega) le_rfl CheckTable.P16

end BMO9.Stages
