/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.WordLink
import Collatz.BMO.Problem9.HighPath

/-!
# BMO #9, port of Rocq `Module WordBlocks` (BMO9.v lines 2865-3021, ccz181078)

Summaries of kernel words as `Block` folds, and certification of a high kernel followed by
low kernels.  Rocq `total depth` (a sum of exponents) is `totalDepth : ℕ`; `total gain` is
`totalGain : ℤ`.
-/

namespace BMO9.WordBlocks

open Table WordLibrary

def depth (k : Kernel) : ℕ := k.pair.d
def totalDepth (w : List Kernel) : ℕ := (w.map depth).sum
def totalGain (w : List Kernel) : ℤ := (w.map gain).sum
def kernels (w : List Kernel) : List Block.Kernel := w.map fun k ↦ TableBridge.kernel k.pair
def summary (w : List Kernel) : Block.Summary := Block.fold (kernels w) Block.identity

theorem totalGain_cons (k : Kernel) (w : List Kernel) :
    totalGain (k :: w) = gain k + totalGain w := by simp [totalGain]

theorem totalDepth_cons (k : Kernel) (w : List Kernel) :
    totalDepth (k :: w) = depth k + totalDepth w := by simp [totalDepth]

theorem totalDepth_le (w : List Kernel) (C : ℕ) (h : ∀ k ∈ w, depth k ≤ C) :
    totalDepth w ≤ w.length * C := by
  induction w with
  | nil => simp [totalDepth]
  | cons k w ih =>
      rw [totalDepth_cons, List.length_cons]
      have := h k (by simp); have := ih (fun z hz ↦ h z (by simp [hz])); nlinarith

theorem totalGain_bound (w : List Kernel) (C : ℤ) (h : ∀ k ∈ w, 0 ≤ gain k ∧ gain k ≤ C) :
    0 ≤ totalGain w ∧ totalGain w ≤ w.length * C := by
  induction w with
  | nil => simp [totalGain]
  | cons k w ih =>
      rw [totalGain_cons, List.length_cons]
      have := h k (by simp); have := ih (fun z hz ↦ h z (by simp [hz])); push_cast
      constructor <;> linarith

theorem fold_added (w : List Kernel) (z : Block.Summary) :
    (Block.fold (kernels w) z).added = z.added + totalGain w := by
  induction w generalizing z with
  | nil => simp [Block.fold, kernels, totalGain]
  | cons k w ih =>
      show (Block.fold (kernels w) (Block.push _ z)).added = _
      rw [ih, totalGain_cons]; simp [Block.push, TableBridge.kernel, gain]; ring

theorem low_fold_added (w : List Kernel) (z : Block.Summary) :
    (Block.low_fold (kernels w) z).added = z.added + totalGain w := by
  induction w generalizing z with
  | nil => simp [Block.low_fold, kernels, totalGain]
  | cons k w ih =>
      show (Block.low_fold (kernels w) (Block.low_push _ z)).added = _
      rw [ih, totalGain_cons]; simp [Block.low_push, TableBridge.kernel, gain]; ring

theorem fold_scale (w : List Kernel) (z : Block.Summary) :
    (Block.fold (kernels w) z).scale = z.scale * 2^totalDepth w := by
  induction w generalizing z with
  | nil => simp [Block.fold, kernels, totalDepth]
  | cons k w ih =>
      show (Block.fold (kernels w) (Block.push _ z)).scale = _
      rw [ih, totalDepth_cons, pow_add]; simp [Block.push, TableBridge.kernel, depth]; ring

theorem fold_strong (ks : List Block.Kernel) (hks : ∀ k ∈ ks, k.Good) (hne : ks ≠ []) :
    ∀ z : Block.Summary, z.Bounded →
      (Block.fold ks z).Bounded ∧ (Block.fold ks z).scale ≤ (Block.fold ks z).sc ∧
        0 < (Block.fold ks z).offset := by
  induction ks with
  | nil => exact absurd rfl hne
  | cons k ks ih =>
      intro z hz
      rcases ks with _ | ⟨a, ks⟩
      · exact Block.push_bounded k z (hks k (by simp)) hz
      · exact ih (fun k' hk' ↦ hks k' (by simp [hk'])) (by simp) _
          (Block.push_bounded k z (hks k (by simp)) hz).1

theorem kernels_good (w : List Kernel) (h : ∀ k ∈ w, Continuing k) :
    ∀ k ∈ kernels w, k.Good := by
  intro k hk
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hk
  exact WordLink.continuing_good z (h z hz)

theorem summary_data (w : List Kernel) (hall : ∀ k ∈ w, Continuing k) (hne : w ≠ []) :
    (summary w).scale = 2^totalDepth w ∧ (summary w).Bounded ∧
    (summary w).scale ≤ (summary w).sc ∧ 0 < (summary w).offset ∧
    (summary w).added = totalGain w := by
  obtain ⟨hb, hA, hC⟩ := fold_strong (kernels w) (kernels_good w hall)
    (by simpa [kernels] using hne) _ Block.identity_bounded
  refine ⟨?_, hb, hA, hC, ?_⟩
  · simp [summary, fold_scale, Block.identity]
  · simp [summary, fold_added, Block.identity]

theorem trace_prefix (xs ys : List Kernel) (S U : ℤ) (h : Trace (xs ++ ys) S U) :
    Trace xs S U := by
  induction xs generalizing S U with
  | nil => exact Trace.nil S U
  | cons k xs ih =>
      cases h with
      | cons ha ht => exact Trace.cons ha (ih _ _ ht)

theorem trace_split (xs ys : List Kernel) (S U : ℤ) (h : Trace (xs ++ ys) S U) :
    ∃ S' U', Block.Calls (kernels xs) S (2*S - U + 3) S' (2*S' - U' + 3) ∧ Trace ys S' U' := by
  induction xs generalizing S U with
  | nil => exact ⟨S, U, Block.Calls.nil _ _, h⟩
  | cons k xs ih =>
      cases h with
      | cons ha ht =>
          obtain ⟨S2, U2, hc, hr⟩ := ih _ _ ht
          exact ⟨S2, U2, Block.Calls.cons (WordLink.action_block _ _ _ _ _ ha) hc, hr⟩

theorem summary_sound (w : List Kernel) (S U S' U' : ℤ)
    (h : Block.Calls (kernels w) S (2*S - U + 3) S' (2*S' - U' + 3)) :
    Block.denotes (summary w) S (2*S - U + 3) S' (2*S' - U' + 3) :=
  Block.fold_sound h Block.identity S (2*S - U + 3) (by simp [Block.denotes, Block.identity])

theorem high_div (m : ℕ) (k : Kernel) (w : List Kernel) (S U : ℤ) (hhigh : m < k.index)
    (htrace : Trace (k :: w) S U) : (2:ℤ)^(m+1) ∣ 2*S - U + 3 := by
  cases htrace with
  | cons ha _ =>
      obtain ⟨-, -, t, ht⟩ := ha
      rw [ht, Table.pow_split k.index (m+1) (by omega)]
      exact Dvd.dvd.mul_right (dvd_mul_right _ _) _

theorem certified_block (m r dL dm : ℕ) (gL gm : ℤ) (k : Kernel) (lows : List Kernel) (S U : ℤ)
    (hgm : 0 ≤ gm) (hhigh : m < k.index) (hk : Continuing k) (hdk : depth k ≤ dL)
    (hgk : gain k ≤ gL)
    (hlow : ∀ z ∈ lows, Continuing z ∧ z.index ≤ m ∧ depth z ≤ dm ∧ gain z ≤ gm)
    (htrace : Trace lows S U) (hbound : WordLink.Bound m r) :
    HighPath.certified m (dL + r*dm) (gL + r*gm) (r*gm) (summary (k :: lows)) := by
  have hall : ∀ z ∈ k :: lows, Continuing z := by
    intro z hz; rcases List.mem_cons.1 hz with rfl | hz
    · exact hk
    · exact (hlow z hz).1
  have hlen : (lows.length : ℤ) ≤ r :=
    hbound lows S U (fun z hz ↦ ⟨(hlow z hz).1, (hlow z hz).2.1⟩) htrace
  have hlen' : lows.length ≤ r := by exact_mod_cast hlen
  have HD : totalDepth lows ≤ r*dm :=
    (totalDepth_le lows dm (fun z hz ↦ (hlow z hz).2.2.1)).trans (Nat.mul_le_mul_right _ hlen')
  have hgpos : ∀ z, Continuing z → 0 ≤ gain z := by
    intro z hz
    obtain ⟨e, hb, -⟩ := hz
    obtain ⟨⟨-, ⟨⟨-, -, -, -, hb1, -⟩, -, hc0⟩, -⟩, -⟩ := built_valid hb
    simp only [gain]; linarith
  obtain ⟨HG0, HG⟩ := totalGain_bound lows gm (fun z hz ↦ ⟨hgpos z (hlow z hz).1, (hlow z hz).2.2.2⟩)
  have HG' : totalGain lows ≤ r*gm := HG.trans (mul_le_mul_of_nonneg_right hlen hgm)
  obtain ⟨HQ, Hb, HA, HC, HM⟩ := summary_data _ hall (by simp)
  rw [totalGain_cons] at HM
  have hkg := WordLink.continuing_gain k hk
  have hc := Block.word_contraction (TableBridge.kernel k.pair) (kernels lows)
    (WordLink.continuing_good k hk) (kernels_good lows (fun z hz ↦ (hlow z hz).1))
  rw [low_fold_added] at hc
  change 2*(summary (k :: lows)).offset ≤ (summary (k :: lows)).sc *
    (3*(summary (k :: lows)).added + 2*(Block.identity.added + totalGain lows) + 6) at hc
  simp only [Block.identity, zero_add] at hc
  obtain ⟨HQpos, HAs, HAs2, HMpos, HCpos, HCs⟩ := Hb
  refine ⟨totalDepth (k :: lows), ?_, HQ, HA, HAs2, HC, ?_, ?_, ?_, ?_⟩
  · rw [totalDepth_cons]; omega
  · have : (summary (k :: lows)).added ≤ gL + r*gm := by rw [HM]; linarith
    nlinarith
  · rw [HM]; linarith
  · rw [HM]; linarith
  · nlinarith

end BMO9.WordBlocks
