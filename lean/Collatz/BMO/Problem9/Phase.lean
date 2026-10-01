/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.TableBridge

/-!
# BMO #9, port of Rocq `Module Phase` (BMO9.v lines 2182-2383, ccz181078)

Levels, depths and separations are `ℕ`; the coefficient-gap `gap` and the depth bound `D`
of `span` stay `ℤ` (as in Rocq), so `span` compares `(depth f : ℤ) ≤ D`.
-/

namespace BMO9.Phase

open Table

/-- The small boundary stays at index `s`; the streaming index `K` grows.
The difference of coefficient valuations stays equal to `gap`. -/
def copies (s : ℕ) (r gap : ℤ) (x : Pair) (K : ℕ) (y : Pair) : Prop :=
  y.b = left s r x ∧ y.c = right s r x ∧ (K:ℤ) - y.d = (s:ℤ) - x.d + gap

theorem copies_head (s : ℕ) (r gap : ℤ) (x : Pair) (K : ℕ) (y : Pair) (hx : Sane s x)
    (hr : Odd r) (hg : 1 ≤ gap) (hc : copies s r gap x K y) :
    even_head K y = even_head s x := by
  obtain ⟨hb, -, hd⟩ := hc
  have hlt : y.d < K := by have := hx.1; omega
  rw [TableBridge.head_value s r x hx hr]
  simp only [even_head, head_constant, if_pos hlt, hb]

theorem copies_separated (s : ℕ) (r gap : ℤ) (x : Pair) (K : ℕ) (y : Pair) (t : ℕ) (u : ℤ)
    (hx : Sane s x) (hr : 1 ≤ r) (ho : Odd r) (hg : 1 ≤ gap) (hc : copies s r gap x K y)
    (hsep : Separated s x t u) : Separated K y t (quotient s r x t u) := by
  obtain ⟨-, hQo, hH⟩ := quotient_spec s r x t u hx hr ho hsep
  obtain ⟨hb, hcc, hd⟩ := hc
  obtain ⟨ht, htx, -, -⟩ := hsep
  refine ⟨ht, by omega, ?_, hQo⟩
  simp only [h, hb, hcc]; exact hH

theorem copies_next (s : ℕ) (r gap : ℤ) (x : Pair) (K : ℕ) (y : Pair) (t : ℕ) (u : ℤ)
    (z : Pair) (_hx : Sane s x) (hc : copies s r gap x K y) (hsep : Separated s x t u)
    (hz : TablePair t z) :
    copies s r gap (next x t u z) (K+1) (widen (next y t (quotient s r x t u) z)) := by
  have HL := next_left s r x t u z hsep hz
  have HB : (widen (next y t (quotient s r x t u) z)).b = left s r (next x t u z) := by
    rw [← HL]; simp only [widen, next, delta, left, coefficient]
  have HM := next_mass x t u z
  have HN := next_mass y t (quotient s r x t u) z
  have HS := values_sum s r x
  have HT := values_sum s r (next x t u z)
  obtain ⟨hb, hcc, hd⟩ := hc
  refine ⟨HB, ?_, ?_⟩
  · simp only [widen] at HB ⊢; linarith
  · simp only [widen, next]; push_cast; omega

/-- `span` includes both endpoints, so a later induction may stop in the
middle of a copied stage without using its final singleton. -/
def span (K n : ℕ) (D : ℤ) : Prop :=
  ∀ i, i ≤ n → ∃ f, Built (K+i) f ∧ (CheckTable.depth f : ℤ) ≤ D

theorem span_one (K : ℕ) (y : Pair) (e v f : ℤ) (D : ℤ) (h0 : Built K (.two y e))
    (h1 : Built (K+1) (.one v f)) (hD : (y.d : ℤ) ≤ D) (hD0 : 0 ≤ D) : span K 1 D := by
  intro i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · exact ⟨_, h0, hD⟩
  · exact ⟨_, h1, by simpa [CheckTable.depth] using hD0⟩

theorem span_prepend (K : ℕ) (f : Entry) (n : ℕ) (D : ℤ) (h0 : Built K f)
    (hD : (CheckTable.depth f : ℤ) ≤ D) (htail : span (K+1) n D) : span K (1+n) D := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact ⟨f, h0, hD⟩
  · obtain ⟨g, hg, hdg⟩ := htail (i-1) (by omega)
    exact ⟨g, by rwa [show K+1+(i-1) = K+i by omega] at hg, hdg⟩

theorem boundary_copy (s : ℕ) (x : Pair) (f : ℤ) (n : ℕ) (H : Boundary Built s x f n) :
    Sane s x → ∀ (r gap : ℤ) (K : ℕ) (y : Pair) (e : ℤ), 1 ≤ r → Odd r → 1 ≤ gap →
      copies s r gap x K y → Built K (.two y e) →
      Built (K+n) (.one (y.b + y.c + 3*f) (e+f)) ∧
        span K n ((K:ℤ) - s - gap + s + n - 1) := by
  induction H with
  | @even x he =>
      intro hx r gap K y e hr hro hg hcopy hlarge
      have HP := copies_head s r gap x K y hx hro hg hcopy
      have HB : Built (K+1) (.one (y.b + y.c + 3*1) (e+1)) := by
        simpa using Built.even hlarge (HP.trans he)
      refine ⟨HB, span_one K y e _ _ _ hlarge HB ?_ ?_⟩ <;>
        · obtain ⟨-, -, hd⟩ := hcopy; have := hx.1; push_cast; omega
  | @one x t u v f' hsep ho hsmall =>
      intro hx r gap K y e hr hro hg hcopy hlarge
      have HP := copies_head s r gap x K y hx hro hg hcopy
      have HS := copies_separated s r gap x K y t u hx hr hro hg hcopy hsep
      have HB := Built.lookup_one hlarge HS (HP.trans ho) hsmall
      obtain ⟨⟨hf, hv⟩, -⟩ := built_valid hsmall
      have HB' : Built (K+1) (.one (y.b + y.c + 3*(1+f')) (e+(1+f'))) := by
        convert HB using 2 <;> omega
      refine ⟨HB', span_one K y e _ _ _ hlarge HB' ?_ ?_⟩ <;>
        · obtain ⟨-, -, hd⟩ := hcopy; have := hx.1; push_cast; omega
  | @two x t u z f' g n hsep ho hsmall _ ih =>
      intro hx r gap K y e hr hro hg hcopy hlarge
      obtain ⟨⟨hf, hz, hmass⟩, -⟩ := built_valid hsmall
      have HP := copies_head s r gap x K y hx hro hg hcopy
      have HS := copies_separated s r gap x K y t u hx hr hro hg hcopy hsep
      have HB := Built.lookup_two hlarge HS (HP.trans ho) hsmall
      have HC := copies_next s r gap x K y t u z hx hcopy hsep hz
      obtain ⟨hend, hspan⟩ := ih (next_sane s x t u z hx hsep hz).1 r gap (K+1) _ (e+1+f')
        hr hro hg HC HB
      have HM := next_mass y t (quotient s r x t u) z
      refine ⟨?_, ?_⟩
      · rw [show K+(1+n) = K+1+n by omega]
        convert hend using 2
        · simp only [widen]; linarith
        · ring
      · apply span_prepend K _ _ _ hlarge
        · obtain ⟨-, -, hd⟩ := hcopy; have := hx.1
          simp only [CheckTable.depth]; push_cast; omega
        · convert hspan using 1; push_cast; ring

theorem span_mono (K n : ℕ) (D D' : ℤ) (hD : D ≤ D') (h : span K n D) : span K n D' := by
  intro i hi
  obtain ⟨f, hf, hd⟩ := h i hi
  exact ⟨f, hf, hd.trans hD⟩

theorem span_zero (K : ℕ) (f : Entry) (D : ℤ) (hf : Built K f)
    (hd : (CheckTable.depth f : ℤ) ≤ D) : span K 0 D := by
  intro i hi
  obtain rfl : i = 0 := by omega
  exact ⟨f, hf, hd⟩

theorem initial_head (l : ℕ) (B : ℤ) (hl : 1 ≤ l) :
    even_head (l+1) ⟨1, 1, B, 0⟩ = (B % 2 == 0) := by
  simp only [even_head, head_constant, if_pos (show 1 < l+1 by omega)]

theorem initial_separated (l : ℕ) (B : ℤ) (s : ℕ) (r : ℤ) (hs : 1 ≤ s ∧ s < l)
    (hB : B + 3 = 2^s*r) (hr : Odd r) : Separated (l+1) ⟨1, 1, B, 0⟩ s r :=
  ⟨hs.1, by simp; omega, by simp [h, hB], hr⟩

theorem initial_copies (l : ℕ) (B : ℤ) (s : ℕ) (r : ℤ) (x : Pair) (hB : B + 3 = 2^s*r) :
    copies s r ((l:ℤ) - s) (lower x) (l+2) (widen (next ⟨1, 1, B, 0⟩ s r x)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [widen, next, delta, lower, left, coefficient]
  · simp only [widen, next, delta, lower, right, coefficient, h]
    linear_combination hB
  · simp only [widen, next, lower]; push_cast; ring

theorem odd_factor (B : ℤ) (s : ℕ) (r : ℤ) (hs : 1 ≤ s) (hB : B + 3 = 2^s*r) : Odd B := by
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s-1, by omega⟩
  exact ⟨2^j*r - 2, by rw [pow_succ] at hB; linarith⟩

theorem stage_even (l : ℕ) (B e : ℤ) (hl : 1 ≤ l) (hB : Built l (.one B e)) (he : Even B) :
    Built (l+2) (.one (B+3) (e+1)) ∧ span l 2 1 := by
  have H1 := Built.one hB
  have H2 : Built (l+1+1) (.one (B+3) (e+1)) := by
    have := Built.even H1 (by rw [initial_head l B hl]; simpa [Int.even_iff] using he)
    simpa using this
  refine ⟨H2, ?_⟩
  apply span_prepend l _ 1 1 hB (by simp [CheckTable.depth])
  apply span_prepend (l+1) _ 0 1 H1 (by simp [CheckTable.depth])
  exact span_zero _ _ _ H2 (by simp [CheckTable.depth])

theorem stage_odd (l : ℕ) (B e : ℤ) (s : ℕ) (r : ℤ) (g : Entry) (hB : Built l (.one B e))
    (hs : 1 ≤ s ∧ s < l) (hfactor : B + 3 = 2^s*r) (hr : Odd r) (hg : Built s g)
    (hreturn : Returns Built s g) :
    ∃ (n : ℕ) (v f : ℤ), n ≤ s ∧ Built (l+2+n) (.one v f) ∧ span l (2+n) (2*s+1) := by
  obtain ⟨⟨he, hBm⟩, -⟩ := built_valid hB
  have hP : (0:ℤ) < 2^s := by positivity
  have hr0 : 1 ≤ r := by nlinarith
  have H1 := Built.one hB
  have HS := initial_separated l B s r hs hfactor hr
  have HO : even_head (l+1) ⟨1, 1, B, 0⟩ = false := by
    rw [initial_head l B (by omega)]
    obtain ⟨j, hj⟩ := odd_factor B s r hs.1 hfactor
    simp; omega
  have hprefix : ∀ n, span (l+2) n (2*s+1) → span l (2+n) (2*s+1) := by
    intro n hspan
    rw [show 2+n = 1+(1+n) by omega]
    apply span_prepend l _ _ _ hB (by simp [CheckTable.depth]; omega)
    apply span_prepend (l+1) _ _ _ H1 (by simp [CheckTable.depth])
    exact hspan
  cases g with
  | one v f =>
      have H2 := Built.lookup_one H1 HS HO hg
      refine ⟨0, _, _, by omega, by simpa using H2, hprefix 0 ?_⟩
      exact span_zero _ _ _ (by simpa using H2) (by simp [CheckTable.depth]; omega)
  | two x f =>
      have H2 := Built.lookup_two H1 HS HO hg
      obtain ⟨⟨hf, hx, hmass⟩, -⟩ := built_valid hg
      obtain ⟨j, n, hbound⟩ := hreturn
      have hlow := lower_sane s x hx
      obtain ⟨hj, hn, -⟩ := boundary_spec Built s _ _ _ (fun _ _ h ↦ built_valid h) hbound hlow
      have hd := pair_depth s _ hlow
      obtain ⟨hend, hspan⟩ := boundary_copy _ _ _ _ hbound hlow r ((l:ℤ) - s) (l+2)
        (widen (next ⟨1, 1, B, 0⟩ s r x)) (e+1+f) hr0 hr (by omega)
        (initial_copies l B s r x hfactor) (by simpa using H2)
      refine ⟨n, _, _, by omega, hend, hprefix n (span_mono _ _ _ _ ?_ hspan)⟩
      push_cast; omega

end BMO9.Phase
