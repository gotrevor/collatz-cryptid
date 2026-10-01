/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.WordArith

/-!
# BMO #9, port of Rocq `Module WordRelation` (BMO9.v lines 1662-1867, ccz181078)

A relation `z` records two dyadic congruences on the unknowns `S, U`:
`q*U ≡ a*S + c (mod 2^n)` and `sa*S ≡ sb (mod 2^sn)`.  The exponents `n, sn` are `ℕ`
(so the Rocq side conditions `0 ≤ n`, `0 ≤ sn` disappear).
-/

namespace BMO9.WordRelation

open WordArith

structure Relation where
  a : ℤ
  q : ℤ
  c : ℤ
  n : ℕ
  sa : ℤ
  sb : ℤ
  sn : ℕ
  deriving DecidableEq, Repr

def Holds (z : Relation) (S U : ℤ) : Prop :=
  Odd z.q ∧ Odd z.sa ∧ div2 z.n (z.q*U - z.a*S - z.c) ∧ div2 z.sn (z.sa*S - z.sb)

def choose (z : Relation) (A Q C : ℤ) (N : ℕ) (a0 b0 : ℤ) (p0 : ℕ) : Relation :=
  if z.n < N then ⟨A, Q, C, N, a0, b0, p0⟩ else ⟨z.a, z.q, z.c, z.n, a0, b0, p0⟩

theorem choose_spec (z : Relation) (A Q C : ℤ) (N : ℕ) (a0 b0 : ℤ) (p0 : ℕ) (S U : ℤ)
    (hz : Holds z S U) (hQ : Odd Q) (hR : div2 N (Q*U - A*S - C)) (ha0 : Odd a0)
    (hS : div2 p0 (a0*S - b0)) : Holds (choose z A Q C N a0 b0 p0) S U := by
  obtain ⟨hq, -, hr, -⟩ := hz
  unfold choose; split_ifs
  · exact ⟨hQ, ha0, hR, hS⟩
  · exact ⟨hq, ha0, hr, hS⟩

theorem eliminate (z : Relation) (A Q C : ℤ) (N : ℕ) (S U : ℤ) (hz : Holds z S U)
    (hnew : div2 N (Q*U - A*S - C)) :
    div2 (min N z.n) ((Q*z.a - z.q*A)*S - (z.q*C - Q*z.c)) := by
  obtain ⟨-, -, hr, -⟩ := hz
  have hr' := div2_weaken z.n (min N z.n) _ (min_le_right _ _) hr
  have hn' := div2_weaken N (min N z.n) _ (min_le_left _ _) hnew
  have H := div2_sub _ _ _ (div2_scale _ _ z.q hn') (div2_scale _ _ Q hr')
  rwa [show z.q*(Q*U - A*S - C) - Q*(z.q*U - z.a*S - z.c) =
    (Q*z.a - z.q*A)*S - (z.q*C - Q*z.c) by ring] at H

theorem check_constant (m : ℕ) (A B S : ℤ) (H : div2 m (A*S - B)) : div2 (order m A) B := by
  have hA := div2_scale _ _ S (order_div m A)
  have hB := div2_weaken m (order m A) _ (order_bound m A) H
  have := div2_sub _ _ _ hA hB
  rwa [show S*A - (A*S - B) = B by ring] at this

theorem divided_constraint (m : ℕ) (A B S : ℤ) (H : div2 m (A*S - B)) :
    div2 (m - order m A) (A / 2^order m A * S - B / 2^order m A) := by
  have hA := div2_shift _ _ (order_div m A)
  have hB := div2_shift _ _ (check_constant _ _ _ _ H)
  apply div2_cancel m (order m A) _ (order_bound m A)
  rw [show 2^order m A*(A / 2^order m A * S - B / 2^order m A) =
    (2^order m A*(A / 2^order m A))*S - 2^order m A*(B / 2^order m A) by ring, ← hA, ← hB]
  exact H

theorem compatible (m : ℕ) (a0 b0 : ℤ) (p0 : ℕ) (a1 b1 S : ℤ)
    (H0 : div2 m (a0*S - b0)) (H1 : div2 p0 (a1*S - b1)) :
    div2 (min m p0) (a0*b1 - a1*b0) := by
  have H0' := div2_weaken m (min m p0) _ (min_le_left _ _) H0
  have H1' := div2_weaken p0 (min m p0) _ (min_le_right _ _) H1
  have H := div2_sub _ _ _ (div2_scale _ _ a1 H0') (div2_scale _ _ a0 H1')
  rwa [show a1*(a0*S - b0) - a0*(a1*S - b1) = a0*b1 - a1*b0 by ring] at H

def intersect (z : Relation) (A Q C : ℤ) (N : ℕ) : Option Relation :=
  let m := min N z.n
  let aa := Q*z.a - z.q*A
  let bb := z.q*C - Q*z.c
  let v := order m aa
  if divides v bb then
    if v < m then
      let ca := aa / 2^v
      let cb := bb / 2^v
      let cp := m - v
      if divides (min cp z.sn) (ca*z.sb - z.sa*cb) then
        if z.sn < cp then some (choose z A Q C N ca cb cp)
        else some (choose z A Q C N z.sa z.sb z.sn)
      else none
    else some (choose z A Q C N z.sa z.sb z.sn)
  else none

theorem intersect_spec (z : Relation) (A Q C : ℤ) (N : ℕ) (S U : ℤ) (hz : Holds z S U)
    (hQ : Odd Q) (hnew : div2 N (Q*U - A*S - C)) :
    ∃ z', intersect z A Q C N = some z' ∧ Holds z' S U := by
  have helim := eliminate _ _ _ _ _ _ _ hz hnew
  obtain ⟨hq, ha, hU, hS⟩ := hz
  have hz : Holds z S U := ⟨hq, ha, hU, hS⟩
  set m := min N z.n
  set aa := Q*z.a - z.q*A
  set bb := z.q*C - Q*z.c
  have hv := order_bound m aa
  have hB := check_constant _ _ _ _ helim
  have hdiv := divided_constraint _ _ _ _ helim
  have htest : divides (order m aa) bb = true := (divides_spec _ _).2 hB
  unfold intersect; dsimp only
  rw [if_pos (show divides (order (min N z.n) (Q*z.a - z.q*A)) (z.q*C - Q*z.c) = true
    from htest)]
  split_ifs with hlt hc hsn
  · exact ⟨_, rfl, choose_spec _ _ _ _ _ _ _ _ _ _ hz hQ hnew (order_shift_odd _ _ hlt) hdiv⟩
  · exact ⟨_, rfl, choose_spec _ _ _ _ _ _ _ _ _ _ hz hQ hnew ha hS⟩
  · exact absurd ((divides_spec _ _).2 (compatible _ _ _ _ _ _ S hdiv hS)) hc
  · exact ⟨_, rfl, choose_spec _ _ _ _ _ _ _ _ _ _ hz hQ hnew ha hS⟩

def Optional (z : Option Relation) (S U : ℤ) : Prop :=
  match z with
  | none => True
  | some z => Holds z S U

def add (z : Option Relation) (A Q C : ℤ) (N : ℕ) : Option Relation :=
  match z with
  | none => some ⟨A, Q, C, N, 1, 0, 0⟩
  | some z => intersect z A Q C N

theorem add_spec (z : Option Relation) (A Q C : ℤ) (N : ℕ) (S U : ℤ) (hz : Optional z S U)
    (hQ : Odd Q) (hnew : div2 N (Q*U - A*S - C)) :
    ∃ z', add z A Q C N = some z' ∧ Holds z' S U := by
  cases z with
  | some z => exact intersect_spec z A Q C N S U hz hQ hnew
  | none => exact ⟨_, rfl, hQ, odd_one, hnew, div2_refl _⟩

/-! The old constraints force the valuation of the next head expression, or a lower bound
for it.  No finite bound on `S` or `U` is assumed. -/

def elim_a (z : Relation) (A Q : ℤ) : ℤ := Q*z.a - z.q*A
def elim_b (z : Relation) (B Q : ℤ) : ℤ := z.q*B - Q*z.c
def cutoff (z : Relation) (A Q : ℤ) : ℕ := min z.n (z.sn + order z.n (elim_a z A Q))
def residual (z : Relation) (A B Q : ℤ) : ℤ := z.sa*elim_b z B Q - elim_a z A Q*z.sb

theorem pruning_constraint (z : Relation) (A B Q S U H : ℤ) (hz : Holds z S U)
    (hH : H = A*S - Q*U + B) :
    div2 (cutoff z A Q) (residual z A B Q - z.sa*z.q*H) := by
  obtain ⟨-, -, hU, hS⟩ := hz
  have hmul := div2_product _ _ _ _ hS (order_div z.n (elim_a z A Q))
  have hmul' := div2_weaken _ (cutoff z A Q) _ (min_le_right _ _) hmul
  have hsc := div2_scale _ _ (z.sa*Q) hU
  have hsc' := div2_weaken z.n (cutoff z A Q) _ (min_le_left _ _) hsc
  have hsum := div2_add _ _ _ hmul' hsc'
  convert hsum using 1
  simp only [residual, elim_a, elim_b, hH]; ring

theorem pruning_spec (z : Relation) (A B Q S U : ℤ) (D s : ℕ) (t : ℤ) (hz : Holds z S U)
    (hH : A*S - Q*U + B = 2^(D+s)*(2*t+1)) :
    let bound := cutoff z A Q
    let v := order bound (residual z A B Q)
    (v < bound → s + D = v) ∧ (v = bound → bound ≤ D + s) := by
  dsimp only
  have hdiv := pruning_constraint z A B Q S U _ hz hH.symm
  obtain ⟨hQ, ha, -, -⟩ := hz
  have hodd : Odd (z.sa*z.q*(2*t+1)) := (ha.mul hQ).mul (odd_two_mul_add_one t)
  rw [show residual z A B Q - z.sa*z.q*(2^(D+s)*(2*t+1)) =
    residual z A B Q - 2^(D+s)*(z.sa*z.q*(2*t+1)) by ring] at hdiv
  obtain ⟨he, hle⟩ := order_compatible _ _ _ _ hodd hdiv
  exact ⟨fun h ↦ by have := he h; omega, fun h ↦ by have := hle h; omega⟩

end BMO9.WordRelation
