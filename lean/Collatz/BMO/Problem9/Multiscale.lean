/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.WordBlocks

/-!
# BMO #9, port of Rocq `Module Multiscale` (BMO9.v lines 3022-3119, ccz181078)

Lifting a word-length bound at a low level `m` to a higher level `L`.  The low bound `r`, the
depth parameters and the counts `t, q` are `ℕ` (they enter exponents or lengths); gains are `ℤ`.
-/

namespace BMO9.Multiscale

open Table WordLibrary WordBlocks

/-- Rocq `parameters L d g`. -/
def Parameters (L d : ℕ) (g : ℤ) : Prop :=
  ∀ k, Continuing k → k.index ≤ L → depth k ≤ d ∧ gain k ≤ g

theorem low_split (m : ℕ) (w : List Kernel) : ∃ lows tail, w = lows ++ tail ∧
    (∀ k ∈ lows, k.index ≤ m) ∧ (tail = [] ∨ ∃ k rest, tail = k :: rest ∧ m < k.index) := by
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | cons k w ih =>
      by_cases hk : k.index ≤ m
      · obtain ⟨lows, tail, rfl, hl, ht⟩ := ih
        exact ⟨k :: lows, tail, rfl, by simp [hk]; exact hl, ht⟩
      · exact ⟨[], k :: w, rfl, by simp, Or.inr ⟨k, w, rfl, by omega⟩⟩

theorem high_decompose (m L r dL dm : ℕ) (gL gm : ℤ) (hgm : 0 ≤ gm)
    (hglobal : Parameters L dL gL) (hlow : Parameters m dm gm) (hbound : WordLink.Bound m r) :
    ∀ fuel k rest S U, (k :: rest).length ≤ fuel → m < k.index →
      (∀ z ∈ k :: rest, Continuing z ∧ z.index ≤ L) → Trace (k :: rest) S U →
      ∃ zs, HighPath.path m (dL + r*dm) (gL + r*gm) (r*gm) zs S (2*S - U + 3) ∧
        (k :: rest).length ≤ (r+1)*(zs.length + 1) := by
  intro fuel
  induction fuel with
  | zero => intro k rest S U hf; simp at hf
  | succ fuel ih =>
    intro k rest Sa Ua hfuel hhigh hall htrace
    obtain ⟨lows, tail, rfl, hind, htail⟩ := low_split m rest
    have hdiv := high_div m k (lows ++ tail) Sa Ua hhigh htrace
    have hk := hall k (by simp)
    have hlows : ∀ z ∈ lows, Continuing z ∧ z.index ≤ L :=
      fun z hz ↦ hall z (by simp [hz])
    have htailall : ∀ z ∈ tail, Continuing z ∧ z.index ≤ L :=
      fun z hz ↦ hall z (by simp [hz])
    cases htrace with
    | @cons _ _ _ _ S1 U1 hfirst hafter =>
    have hlowtrace := trace_prefix lows tail S1 U1 hafter
    have hlen : (lows.length : ℤ) ≤ r :=
      hbound lows S1 U1 (fun z hz ↦ ⟨(hlows z hz).1, hind z hz⟩) hlowtrace
    have hlen' : lows.length ≤ r := by exact_mod_cast hlen
    rcases htail with rfl | ⟨k', rest', rfl, hhigh'⟩
    · refine ⟨[], HighPath.path.stop _ _ hdiv, ?_⟩
      simp; omega
    · obtain ⟨Sb, Ub, hcalls, hresttrace⟩ :=
        trace_split (k :: lows) (k' :: rest') Sa Ua (Trace.cons hfirst hafter)
      obtain ⟨zs, hpath, hcount⟩ := ih k' rest' Sb Ub
        (by simp at hfuel ⊢; omega) hhigh' htailall hresttrace
      refine ⟨summary (k :: lows) :: zs, ?_, ?_⟩
      · obtain ⟨hS, hH⟩ := summary_sound _ _ _ _ _ hcalls
        subst hS
        refine HighPath.path.step _ _ _ _ _ hdiv ?_ ⟨rfl, hH⟩ hpath
        obtain ⟨hd, hg⟩ := hglobal k hk.1 hk.2
        exact certified_block m r dL dm gL gm k lows S1 U1 hgm hhigh hk.1 hd hg
          (fun z hz ↦ ⟨(hlows z hz).1, hind z hz,
            hlow z (hlows z hz).1 (hind z hz)⟩) hlowtrace hbound
      · simp only [List.length_cons, List.length_append] at hcount ⊢
        nlinarith

theorem lift_bound (m L r dL dm : ℕ) (gL gm : ℤ) (t q : ℕ) (hm : 0 < m) (hgm : 0 ≤ gm)
    (hgL : 0 ≤ gL) (hglobal : Parameters L dL gL) (hlow : Parameters m dm gm)
    (hbound : WordLink.Bound m r)
    (hbudget : 2^(2*(dL + r*dm))*(12*(gL + r*gm) + 8) < (2:ℤ)^(m+1))
    (hpow : 2*(gL + r*gm) + 2 ≤ 3^t) (hq : r*gm + 4 ≤ q*(m:ℤ)) :
    WordLink.Bound L (((r+1)*(t+q+2) + r : ℕ) : ℤ) := by
  intro w S U hall htrace
  obtain ⟨lows, tail, rfl, hind, htail⟩ := low_split m w
  have hlows : ∀ z ∈ lows, Continuing z ∧ z.index ≤ L := fun z hz ↦ hall z (by simp [hz])
  have htailall : ∀ z ∈ tail, Continuing z ∧ z.index ≤ L := fun z hz ↦ hall z (by simp [hz])
  have hlowtrace := trace_prefix lows tail S U htrace
  have hlen : (lows.length : ℤ) ≤ r :=
    hbound lows S U (fun z hz ↦ ⟨(hlows z hz).1, hind z hz⟩) hlowtrace
  have hlen' : lows.length ≤ r := by exact_mod_cast hlen
  rcases htail with rfl | ⟨k, rest, rfl, hhigh⟩
  · simp only [List.append_nil]
    have : lows.length ≤ (r+1)*(t+q+2) + r := by nlinarith
    exact_mod_cast this
  · obtain ⟨S', U', hsuf⟩ := WordLink.trace_suffix lows (k :: rest) S U htrace
    obtain ⟨zs, hpath, hcount⟩ := high_decompose m L r dL dm gL gm hgm hglobal hlow hbound
      _ k rest S' U' le_rfl hhigh htailall hsuf
    have hgr : (0:ℤ) ≤ r*gm := by positivity
    have hzs := HighPath.path_count m (dL + r*dm) (gL + r*gm) (r*gm) zs S' (2*S' - U' + 3) t q
      hm hgr (by linarith) hpow hq hbudget hpath
    have : (lows ++ k :: rest).length ≤ (r+1)*(t+q+2) + r := by
      rw [List.length_append]
      have : (r+1)*(zs.length+1) ≤ (r+1)*(t+q+2) := Nat.mul_le_mul_left _ (by omega)
      omega
    exact_mod_cast this

end BMO9.Multiscale
