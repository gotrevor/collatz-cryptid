/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.BoundaryBound
import Collatz.BMO.Problem9.Stages
import Collatz.BMO.Problem9.TableBridge

/-!
# BMO #9, port of Rocq `Module Closure` (BMO9.v lines 2659-2740, ccz181078)

The single induction step: every level is `good` (built, bounded, returning), given a budget
for levels above 65536.
-/

namespace BMO9.Closure

open Table

def Good (k : ℕ) : Prop := ∃ f, Built k f ∧ CheckTable.Bounded k f ∧ Returns Built k f

def Earlier (k : ℕ) : Prop := ∀ s, 1 ≤ s → s < k → Good s

def Budget (k : ℕ) : Prop :=
  ∃ L n : ℕ, 1 ≤ L ∧ L < k ∧ WordLink.Bound L ((n:ℤ) - 1) ∧
    6*(CheckTable.log2up k : ℤ) + 9 + n*(6*(CheckTable.log2up L : ℤ) + 9) + L < k ∧
    2*(12*(k:ℤ)^3 + n*(12*(L:ℤ)^3 + 3)) + 3 < 2^L

theorem earlier_bounds (k : ℕ) (h : Earlier k) (s : ℕ) (f : Entry) (hs1 : 1 ≤ s) (hs : s < k)
    (hf : Built s f) : CheckTable.Bounded s f := by
  obtain ⟨g, hg, hb, -⟩ := h s hs1 hs
  rwa [UniqueTable.built_unique hf g hg]

theorem kernel_bounds (k L : ℕ) (_hL1 : 1 ≤ L) (hL : L < k) (hprev : Earlier k) (s : ℕ) (y : Pair)
    (e : ℤ) (hs1 : 1 ≤ s) (hs : s ≤ L) (hb : Built s (.two y e)) :
    (y.d : ℤ) ≤ 6*(CheckTable.log2up L : ℤ) + 9 ∧ y.b + y.c + 2 ≤ 12*(L:ℤ)^3 + 3 := by
  obtain ⟨hE, hD⟩ := earlier_bounds k hprev s _ hs1 (by omega) hb
  simp only [steps, CheckTable.depth] at hE hD
  have hlog : CheckTable.log2up s ≤ CheckTable.log2up L := Nat.clog_mono_right 2 hs
  have hpow : (s:ℤ)^3 ≤ (L:ℤ)^3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) 3
  obtain ⟨⟨he0, hy, hmass⟩, -⟩ := built_valid hb
  constructor
  · have : (y.d : ℤ) ≤ 6*(CheckTable.log2up s : ℤ) + 9 := by exact_mod_cast hD
    have : (CheckTable.log2up s : ℤ) ≤ CheckTable.log2up L := by exact_mod_cast hlog
    linarith
  · linarith

/-- The single induction step. -/
theorem close (k : ℕ) (_hk : 1 ≤ k) (hprev : Earlier k) (hbud : Budget k) : Good k := by
  obtain ⟨L, n, hL1, hLk, hword, hdepth, hmass⟩ := hbud
  have hentries : ∀ s, 1 ≤ s → s < k → ∃ f, Built s f ∧ Returns Built s f := by
    intro s hs1 hs
    obtain ⟨f, hf, -, hr⟩ := hprev s hs1 hs
    exact ⟨f, hf, hr⟩
  obtain ⟨f, hf, hbounds⟩ := Stages.through k hentries
  refine ⟨f, hf, hbounds, ?_⟩
  cases f with
  | one => trivial
  | two x e =>
      obtain ⟨hE, hD⟩ := hbounds
      simp only [steps, CheckTable.depth] at hE hD
      obtain ⟨⟨he0, hx, hsum⟩, -⟩ := built_valid hf
      have hD' : (x.d : ℤ) ≤ 6*(CheckTable.log2up k : ℤ) + 9 := by exact_mod_cast hD
      have hlogL : (0:ℤ) ≤ CheckTable.log2up L := by positivity
      exact BoundaryBound.returns_of_bound k (lower x) L (6*(CheckTable.log2up L : ℤ) + 9)
        (12*(L:ℤ)^3 + 3) n hL1 (by linarith) (by positivity) (lower_sane k x hx)
        (fun s hs1 hs ↦ by
          obtain ⟨g, hg, -⟩ := hentries s hs1 (by omega)
          exact ⟨g, hg⟩)
        (fun s y e hs1 hs hb ↦ kernel_bounds k L hL1 hLk hprev s y e hs1 hs hb)
        hword (by simp only [lower]; linarith) (by simp only [lower]; nlinarith)

theorem induction_step (k : ℕ) (hk : 1 ≤ k) (hprev : Earlier k)
    (hbud : 65536 < k → Budget k) : Good k := by
  by_cases hsmall : k ≤ 65536
  · exact CheckTable.base_structured k hk hsmall
  · exact close k hk hprev (hbud (by omega))

theorem all_good (hbud : ∀ k, 65536 < k → Earlier k → Budget k) : ∀ k, 1 ≤ k → Good k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hk
      have hprev : Earlier k := fun s hs1 hs ↦ ih s hs hs1
      exact induction_step k hk hprev (fun hl ↦ hbud k hl hprev)

theorem G_returns_of (hbud : ∀ k, 65536 < k → Earlier k → Budget k) :
    ∀ k t, ∃ e m, Prefix.Exec e (Prefix.G (k+1) (1+2*t)) [m] := by
  intro k t
  obtain ⟨f, hf, -, hr⟩ := all_good hbud (k+1) (by omega)
  have := Table.G_returns Built (k+1) f (fun _ _ h ↦ built_valid h) (built_valid hf) hr
    (by omega) (1 + 2*(t:ℤ)) (by omega) ⟨t, by ring⟩
  simpa [Table.G, show (1 + 2*(t:ℤ)).toNat = 1 + 2*t by omega] using this

/-- **Open crux.**  Rocq `FinalBudget.budget`. -/
theorem budget : ∀ k, 65536 < k → Earlier k → Budget k := by
  sorry

theorem G_returns : ∀ k t, ∃ e m, Prefix.Exec e (Prefix.G (k+1) (1+2*t)) [m] :=
  G_returns_of budget

end BMO9.Closure
