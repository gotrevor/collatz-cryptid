/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.CheckTable

/-!
# BMO #9, port of Rocq `Module WordArith` (BMO9.v lines 1507-1660, ccz181078)

Dyadic divisibility `div2 n x` (`2^n ∣ x`) and a computable truncated 2-adic valuation
`order n x = min n (v₂ x)` (with `order n 0 = n`).  Exponents are `ℕ`; Rocq `Z.shiftr x n`
becomes `x / 2^n` (ℤ floor division, which agrees with `Z.shiftr`).
-/

namespace BMO9.WordArith

def div2 (n : ℕ) (x : ℤ) : Prop := ∃ q, x = 2^n*q

theorem div2_zero (n : ℕ) : div2 n 0 := ⟨0, by ring⟩

theorem div2_refl (x : ℤ) : div2 0 x := ⟨x, by ring⟩

theorem div2_add (n : ℕ) (x y : ℤ) : div2 n x → div2 n y → div2 n (x+y) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a+b, by ring⟩

theorem div2_sub (n : ℕ) (x y : ℤ) : div2 n x → div2 n y → div2 n (x-y) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a-b, by ring⟩

theorem div2_scale (n : ℕ) (x a : ℤ) : div2 n x → div2 n (a*x) := by
  rintro ⟨b, rfl⟩; exact ⟨a*b, by ring⟩

theorem div2_weaken (n m : ℕ) (x : ℤ) (h : m ≤ n) : div2 n x → div2 m x := by
  rintro ⟨a, rfl⟩; exact ⟨2^(n-m)*a, by rw [Table.pow_split n m h]; ring⟩

theorem div2_product (n m : ℕ) (x y : ℤ) : div2 n x → div2 m y → div2 (n+m) (x*y) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a*b, by ring⟩

theorem div2_cancel (n m : ℕ) (x : ℤ) (h : m ≤ n) : div2 n (2^m*x) → div2 (n-m) x := by
  rintro ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [Table.pow_split n m h, mul_assoc] at ha
  exact mul_left_cancel₀ (by positivity) ha

theorem div2_shift (n : ℕ) (x : ℤ) : div2 n x → x = 2^n*(x / 2^n) := by
  rintro ⟨a, rfl⟩
  rw [Int.mul_ediv_cancel_left _ (by positivity)]

theorem odd_not_div (n : ℕ) (x : ℤ) (hn : 1 ≤ n) (ho : Odd x) : ¬ div2 n x := by
  intro hd
  obtain ⟨b, hb⟩ := div2_weaken n 1 x hn hd
  obtain ⟨a, ha⟩ := ho
  omega

theorem split2_spec (p : ℕ) (hp : p ≠ 0) :
    p = 2^(CheckTable.split2 p).1 * (CheckTable.split2 p).2 ∧ Odd (CheckTable.split2 p).2 := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rw [CheckTable.split2]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := ih (p/2) (by omega) (by omega)
      refine ⟨?_, h2⟩
      dsimp only
      rw [pow_succ, mul_comm (2^_) 2, mul_assoc]
      omega
    · refine ⟨by simp, ?_⟩
      dsimp only
      exact Nat.odd_iff.2 (by omega)

/-- Rocq `order`: `min n (v₂ x)`, and `n` for `x = 0`. -/
def order (n : ℕ) (x : ℤ) : ℕ :=
  if x = 0 then n else min n (CheckTable.split2 x.natAbs).1

theorem order_spec (n : ℕ) (x : ℤ) :
    order n x ≤ n ∧ ∃ q, x = 2^order n x*q ∧ (order n x < n → Odd q) := by
  unfold order
  split_ifs with hx
  · exact ⟨le_rfl, 0, by simp [hx], fun h ↦ absurd h (lt_irrefl _)⟩
  · obtain ⟨he, ho⟩ := split2_spec x.natAbs (by omega)
    set s := (CheckTable.split2 x.natAbs).1
    set r := (CheckTable.split2 x.natAbs).2
    have hx' : x = 2^s*(r:ℤ) ∨ x = -(2^s*(r:ℤ)) := by
      rcases Int.natAbs_eq x with h | h <;> rw [h, he] <;> push_cast <;> simp
    refine ⟨min_le_left _ _, ?_⟩
    rcases le_total n s with hns | hns
    · rw [min_eq_left hns]
      refine ⟨(if x = 2^s*(r:ℤ) then 1 else -1)*2^(s-n)*r, ?_, fun h ↦ absurd h (lt_irrefl _)⟩
      have := Table.pow_split s n hns
      split_ifs with h
      · rw [h, this]; ring
      · rcases hx' with h' | h'
        · exact absurd h' h
        · rw [h', this]; ring
    · rw [min_eq_right hns]
      have hor : Odd (r:ℤ) := by exact_mod_cast ho
      rcases hx' with h' | h'
      · exact ⟨r, h', fun _ ↦ hor⟩
      · exact ⟨-r, by rw [h']; ring, fun _ ↦ hor.neg⟩

theorem order_div (n : ℕ) (x : ℤ) : div2 (order n x) x := by
  obtain ⟨_, q, hq, _⟩ := order_spec n x; exact ⟨q, hq⟩

theorem order_bound (n : ℕ) (x : ℤ) : order n x ≤ n := (order_spec n x).1

theorem order_shift_odd (n : ℕ) (x : ℤ) (hlt : order n x < n) : Odd (x / 2^order n x) := by
  obtain ⟨_, q, hx, ho⟩ := order_spec n x
  have : x / 2^order n x = q := by
    generalize order n x = o at hx ⊢
    subst hx
    exact Int.mul_ediv_cancel_left _ (pow_ne_zero _ two_ne_zero)
  rw [this]; exact ho hlt

theorem div2_order (n : ℕ) (x : ℤ) : div2 n x ↔ order n x = n := by
  obtain ⟨hb, q, hx, hodd⟩ := order_spec n x
  constructor
  · intro h
    by_contra hne
    have hlt : order n x < n := lt_of_le_of_ne hb hne
    rw [hx] at h
    have := div2_cancel n (order n x) q hb h
    exact odd_not_div (n - order n x) q (by omega) (hodd hlt) this
  · intro h
    have := order_div n x
    rwa [h] at this

def divides (n : ℕ) (x : ℤ) : Bool := decide (n ≤ order n x)

theorem divides_spec (n : ℕ) (x : ℤ) : divides n x = true ↔ div2 n x := by
  rw [divides, decide_eq_true_iff, div2_order]
  have := order_bound n x
  omega

theorem order_compatible (n : ℕ) (x : ℤ) (m : ℕ) (q : ℤ) (hq : Odd q)
    (H : div2 n (x - 2^m*q)) :
    (order n x < n → m = order n x) ∧ (order n x = n → n ≤ m) := by
  obtain ⟨hv, a, ha, ho⟩ := order_spec n x
  refine ⟨fun hvlt ↦ ?_, fun hv0 ↦ ?_⟩
  · rcases lt_trichotomy m (order n x) with hlt | he | hgt
    · exfalso
      have H1 : div2 (m+1) x := div2_weaken _ _ _ (by omega) (order_div n x)
      have H2 : div2 (m+1) (x - 2^m*q) := div2_weaken n _ _ (by omega) H
      have H3 : div2 (m+1) (2^m*q) := by
        have := div2_sub _ _ _ H1 H2
        rwa [show x - (x - 2^m*q) = 2^m*q by ring] at this
      have H4 := div2_cancel (m+1) m q (by omega) H3
      exact odd_not_div (m+1-m) q (by omega) hq H4
    · exact he
    · exfalso
      have H1 : div2 (order n x + 1) (2^m*q) := div2_weaken m _ _ (by omega) ⟨q, rfl⟩
      have H2 : div2 (order n x + 1) (x - 2^m*q) := div2_weaken n _ _ (by omega) H
      have H3 : div2 (order n x + 1) (2^order n x*a) := by
        have := div2_add _ _ _ H2 H1
        rwa [show x - 2^m*q + 2^m*q = 2^order n x*a by rw [← ha]; ring] at this
      have H4 := div2_cancel (order n x + 1) (order n x) a (by omega) H3
      exact odd_not_div _ a (by omega) (ho hvlt) H4
  · by_contra hle
    have H1 : div2 n x := (div2_order n x).2 hv0
    have H2 : div2 n (2^m*q) := by
      have := div2_sub _ _ _ H1 H
      rwa [show x - (x - 2^m*q) = 2^m*q by ring] at this
    exact odd_not_div (n-m) q (by omega) hq (div2_cancel n m q (by omega) H2)

end BMO9.WordArith
