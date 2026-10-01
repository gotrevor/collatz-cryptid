/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Prefix

/-!
# BMO #9, port of Rocq `Module Table` (BMO9.v lines 596-1140, ccz181078)

Table entries over integers.  Rocq uses `Z` for the level `k`, the depth `d` and the
separation `s`; here those are exponents, hence `ℕ` (Lean's `ℤ` has no integer exponent).
-/

namespace BMO9.Table

def nums (xs : List ℤ) : List ℕ := xs.map Int.toNat
def F (k : ℕ) (q : ℤ) : List ℕ := Prefix.F k q.toNat
def G (k : ℕ) (q : ℤ) : List ℕ := Prefix.G k q.toNat
def run (e : ℕ) (xs ys : List ℤ) : Prop := Prefix.Run e (nums xs) (nums ys)
def exec (e : ℕ) (xs ys : List ℤ) : Prop := Prefix.Exec e (nums xs) (nums ys)

theorem pow_split (k d : ℕ) (h : d ≤ k) : (2:ℤ)^k = 2^d*2^(k-d) := by
  rw [← pow_add, Nat.add_sub_cancel' h]

theorem run_even (u v w : ℤ) (r : List ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (he : Even u) : run 1 (u :: v :: w :: r) ((u+v+w+3) :: r) := by
  obtain ⟨n, rfl⟩ := he
  have := Prefix.Run.one (Prefix.Step.E n.toNat v.toNat w.toNat (nums r))
  simp only [run, nums, List.map_cons] at this ⊢
  rw [show (n+n).toNat = 2*n.toNat by omega,
    show (n+n+v+w+3).toNat = 2*n.toNat+v.toNat+w.toNat+3 by omega]
  exact this

theorem odd_lookup (u v w : ℤ) (s : ℕ) (q : ℤ) (r : List ℤ) (e : ℕ) (ys : List ℤ) (z : ℤ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (huo : Odd u) (hs : 1 ≤ s) (hq : 3 ≤ q)
    (hqo : Odd q) (hH : u + 2*v + 3 = 2^s*q)
    (hr : Prefix.Run e (F s q) (nums ys ++ [z.toNat])) (hz0 : 0 ≤ z) (hz : 0 ≤ z + w - v - 1) :
    run (1+e) (u :: v :: w :: r) ((ys ++ [z+w-v-1]) ++ r) := by
  obtain ⟨n, rfl⟩ := huo
  obtain ⟨t, rfl⟩ := hqo
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s-1, by omega⟩
  have hhalf : n + v + 2 = 2^s'*(3+2*(t-1)) := by
    rw [pow_succ] at hH; linarith
  have hnat : n.toNat + v.toNat + 2 = 2^s'*(3+2*(t-1).toNat) := by
    have h1 : ((n.toNat + v.toNat + 2 : ℕ) : ℤ) = ((2^s'*(3+2*(t-1).toNat) : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
        Int.toNat_of_nonneg (by omega)]
      exact hhalf
    exact_mod_cast h1
  have hF : F (s'+1) (2*t+1) = Prefix.F (s'+1) (3+2*(t-1).toNat) := by
    simp only [F]; congr 1; omega
  rw [hF] at hr
  have H := Prefix.odd_lookup s' (t-1).toNat n.toNat v.toNat w.toNat (nums r) e _ _ hnat hr
  simp only [run, nums, List.map_append, List.map_cons, List.map_nil] at H ⊢
  rw [show (2*n+1).toNat = 2*n.toNat+1 by omega,
    show (z+w-v-1).toNat = z.toNat + w.toNat - v.toNat - 1 by omega]
  exact H

structure Pair where
  p : ℤ
  d : ℕ
  b : ℤ
  c : ℤ
  deriving DecidableEq, Repr

def coefficient (k : ℕ) (x : Pair) : ℤ := x.p * 2^(k - x.d)
def left (k : ℕ) (q : ℤ) (x : Pair) : ℤ := coefficient k x * q + x.b
def right (k : ℕ) (q : ℤ) (x : Pair) : ℤ := (2^k - coefficient k x) * q + x.c
def values (k : ℕ) (q : ℤ) (x : Pair) : List ℤ := [left k q x, right k q x]
def h (x : Pair) : ℤ := x.b + 2*x.c + 3

def Sane (k : ℕ) (x : Pair) : Prop :=
  x.d ≤ k ∧ 0 < x.p ∧ x.p < 2^x.d ∧ Odd x.p ∧ 1 ≤ x.b ∧ -1 ≤ x.c

def TablePair (k : ℕ) (x : Pair) : Prop := Sane k x ∧ 2*x.p ≤ 2^x.d ∧ 0 ≤ x.c

theorem coefficient_bounds (k : ℕ) (x : Pair) (hx : Sane k x) :
    0 < coefficient k x ∧ coefficient k x < 2^k := by
  obtain ⟨hd, hp, hp2, -, -, -⟩ := hx
  have hP : (0:ℤ) < 2^(k - x.d) := by positivity
  rw [coefficient, pow_split k x.d hd]
  exact ⟨by positivity, mul_lt_mul_of_pos_right hp2 hP⟩

theorem values_nonnegative (k : ℕ) (q : ℤ) (x : Pair) (hx : Sane k x) (hq : 1 ≤ q) :
    1 ≤ left k q x ∧ 0 ≤ right k q x := by
  have := coefficient_bounds k x hx
  obtain ⟨-, -, -, -, hb, hc⟩ := hx
  simp only [left, right]
  constructor <;> nlinarith

theorem h_positive (k : ℕ) (x : Pair) (hx : Sane k x) : 2 ≤ h x := by
  obtain ⟨-, -, -, -, hb, hc⟩ := hx; simp only [h]; omega

def Separated (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) : Prop :=
  1 ≤ s ∧ s + x.d < k ∧ h x = 2^s*r ∧ Odd r

def quotient (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) : ℤ :=
  (2^(x.d+1) - x.p)*2^(k - x.d - s)*q + r

theorem quotient_spec (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) (hx : Sane k x) (hq : 1 ≤ q)
    (_hqo : Odd q) (hs : Separated k x s r) :
    3 ≤ quotient k q x s r ∧ Odd (quotient k q x s r) ∧
      left k q x + 2*right k q x + 3 = 2^s*quotient k q x s r := by
  obtain ⟨hs1, hsk, hh, hr⟩ := hs
  obtain ⟨hd, hp, hp2, -, hb, hc⟩ := hx
  have hsp : (0:ℤ) < 2^s := by positivity
  have hr0 : 1 ≤ r := by
    rcases hr with ⟨j, rfl⟩
    by_contra hcon
    have : 2^s*(2*j+1) ≤ 0 := by nlinarith
    simp only [h] at hh; omega
  obtain ⟨j, hj⟩ : ∃ j, k - x.d - s = j + 1 := ⟨k - x.d - s - 1, by omega⟩
  have hD : (2:ℤ)^(x.d+1) = 2*2^x.d := by ring
  have hJ : (0:ℤ) < 2^j := by positivity
  have hE : (2:ℤ)^(k - x.d - s) = 2*2^j := by rw [hj]; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [quotient, hE, hD]
    have h1 : 1 ≤ 2*2^x.d - x.p := by linarith
    have h2 : 2 ≤ (2*2^x.d - x.p)*(2*2^j) := by nlinarith
    nlinarith
  · simp only [quotient, hE]
    obtain ⟨v, hv⟩ := hr
    exact ⟨(2^(x.d+1) - x.p)*2^j*q + v, by rw [hv]; ring⟩
  · have h1 : (2:ℤ)^k = 2^x.d*2^(k - x.d) := pow_split k x.d hd
    have h2 : (2:ℤ)^(k - x.d) = 2^s*2^(k - x.d - s) := pow_split _ _ (by omega)
    simp only [quotient, left, right, coefficient, h] at hh ⊢
    rw [h1, h2, hD]
    linear_combination hh

theorem values_sum (k : ℕ) (q : ℤ) (x : Pair) :
    left k q x + right k q x = 2^k*q + x.b + x.c := by
  simp only [left, right]; ring

theorem left_odd (k : ℕ) (q : ℤ) (x : Pair) (hd : x.d < k) (hb : Odd x.b) :
    Odd (left k q x) := by
  obtain ⟨t, ht⟩ := hb
  obtain ⟨j, hj⟩ : ∃ j, k - x.d = j + 1 := ⟨k - x.d - 1, by omega⟩
  refine ⟨x.p*2^j*q + t, ?_⟩
  simp only [left, coefficient, ht, hj, pow_succ]; ring

def delta (s : ℕ) (r : ℤ) (y : Pair) : ℤ := y.p*2^(s - y.d)*r

def next (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) : Pair :=
  ⟨y.p*(2^(x.d+1) - x.p), x.d + y.d, delta s r y + y.b, h x - delta s r y + y.c - x.c - 1⟩

def widen (x : Pair) : Pair := ⟨x.p, x.d+1, x.b, x.c⟩

theorem next_mass (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) :
    (next x s r y).b + (next x s r y).c = x.b + x.c + y.b + y.c + 2 := by
  simp only [next, h]; ring

theorem delta_exact (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (hs : Separated k x s r)
    (hy : TablePair s y) : 2^y.d*delta s r y = y.p*h x := by
  rw [hs.2.2.1, delta, pow_split s y.d hy.1.1]; ring

theorem next_sane (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (hx : Sane k x)
    (hs : Separated k x s r) (hy : TablePair s y) :
    Sane k (next x s r y) ∧ 1 ≤ (next x s r y).c := by
  have he := delta_exact k x s r y hs hy
  obtain ⟨hdx, hpx, hpx2, hox, hbx, hcx⟩ := hx
  obtain ⟨hs1, hsk, hh, hr⟩ := hs
  obtain ⟨⟨hdy, hpy, hpy2, hoy, hby, hcy⟩, hhalf, hcy0⟩ := hy
  have hX : (0:ℤ) < 2^x.d := by positivity
  have hY : (0:ℤ) < 2^y.d := by positivity
  have hD : (2:ℤ)^(x.d+1) = 2*2^x.d := by ring
  have hDs : (2:ℤ)^(x.d+y.d) = 2^x.d*2^y.d := pow_add _ _ _
  set z := delta s r y with hz
  simp only [h] at he hh
  have hr0 : 0 < r := by
    by_contra hcon
    have : (2:ℤ)^s*r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have hz0 : 0 ≤ z := by
    simp only [hz, delta]; positivity
  have hnewc : 1 ≤ x.b + 2*x.c + 3 - z + y.c - x.c - 1 := by
    have H1 : 0 ≤ (2^y.d - y.p)*(x.b - 1) := mul_nonneg (by linarith) (by linarith)
    have H2 : 0 ≤ (2^y.d - 2*y.p)*(x.c + 2) := mul_nonneg (by linarith) (by linarith)
    have : 2^y.d*1 ≤ 2^y.d*(x.b + 2*x.c + 3 - z + y.c - x.c - 1) := by nlinarith
    exact le_of_mul_le_mul_left this hY
  simp only [Sane, next, h, hD, hDs]
  refine ⟨⟨by omega, ?_, ?_, ?_, by linarith, by linarith⟩, hnewc⟩
  · exact mul_pos hpy (by linarith)
  · have : y.p*(2*2^x.d - x.p) < y.p*(2*2^x.d) := by nlinarith
    nlinarith
  · exact hoy.mul (by
      obtain ⟨a, ha⟩ := hox
      exact ⟨2^x.d - a - 1, by rw [ha]; ring⟩)

theorem widen_table (k : ℕ) (x : Pair) (hx : Sane k x) (hc : 0 ≤ x.c) :
    TablePair (k+1) (widen x) := by
  obtain ⟨hd, hp, hp2, ho, hb, -⟩ := hx
  simp only [TablePair, Sane, widen, pow_succ]
  refine ⟨⟨by omega, hp, by linarith, ho, hb, by linarith⟩, by linarith, hc⟩

theorem widen_values (k : ℕ) (q : ℤ) (x : Pair) :
    values (k+1) q (widen x) = [left k q x, right k q x + 2^k*q] := by
  simp only [values, widen, left, right, coefficient, Nat.add_sub_add_right, pow_succ]
  congr 2; ring

theorem next_left (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (hs : Separated k x s r)
    (hy : TablePair s y) :
    left s (quotient k q x s r) y = left k q (next x s r y) := by
  obtain ⟨hs1, hsk, -, -⟩ := hs
  have hdy := hy.1.1
  have HP : (2:ℤ)^(s - y.d)*2^(k - x.d - s) = 2^(k - (x.d + y.d)) := by
    rw [← pow_add]; congr 1; omega
  simp only [left, quotient, next, coefficient, delta]
  rw [← HP]; ring

theorem next_right (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (hx : Sane k x)
    (hq : 1 ≤ q) (ho : Odd q) (hs : Separated k x s r) (hy : TablePair s y) :
    right s (quotient k q x s r) y - right k q x - 1 = right k q (next x s r y) := by
  have HH := (quotient_spec k q x s r hx hq ho hs).2.2
  have HL := next_left k q x s r y hs hy
  have HS0 := values_sum k q x
  have HS1 := values_sum s (quotient k q x s r) y
  have HS2 := values_sum k q (next x s r y)
  have HC := next_mass x s r y
  linarith

def head_constant (k : ℕ) (x : Pair) : ℤ := if x.d < k then x.b else x.p + x.b
def even_head (k : ℕ) (x : Pair) : Bool := head_constant k x % 2 == 0

theorem head_parity (k : ℕ) (q : ℤ) (x : Pair) (hx : Sane k x) (hq : Odd q) :
    ∃ a, left k q x = head_constant k x + 2*a := by
  obtain ⟨t, rfl⟩ := hq
  unfold head_constant
  split_ifs with hdk
  · obtain ⟨j, hj⟩ : ∃ j, k - x.d = j + 1 := ⟨k - x.d - 1, by omega⟩
    refine ⟨x.p*2^j*(2*t+1), ?_⟩
    simp only [left, coefficient, hj, pow_succ]; ring
  · have : x.d = k := by have := hx.1; omega
    refine ⟨x.p*t, ?_⟩
    simp only [left, coefficient, this, Nat.sub_self, pow_zero]; ring

theorem even_head_spec (k : ℕ) (q : ℤ) (x : Pair) (hx : Sane k x) (hq : Odd q)
    (he : even_head k x = true) : Even (left k q x) := by
  obtain ⟨a, ha⟩ := head_parity k q x hx hq
  simp only [even_head, beq_iff_eq] at he
  rw [ha]
  exact ⟨head_constant k x / 2 + a, by omega⟩

theorem odd_head_spec (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) (hs : Separated k x s r)
    (he : even_head k x = false) : Odd x.b := by
  have hdk : x.d < k := by have := hs.2.1; omega
  simp only [even_head, head_constant, if_pos hdk, beq_eq_false_iff_ne] at he
  exact Int.odd_iff.2 (by omega)


inductive Entry
  | one (constant count : ℤ)
  | two (state : Pair) (count : ℤ)
  deriving DecidableEq, Repr

def steps : Entry → ℤ
  | .one _ e => e
  | .two _ e => e

def eval (k : ℕ) (q : ℤ) : Entry → List ℤ
  | .one v _ => [2^k*q + v]
  | .two x _ => values k q x

def WellFormed (k : ℕ) : Entry → Prop
  | .one v e => 0 ≤ e ∧ v = 1 + 3*e
  | .two x e => 0 ≤ e ∧ TablePair k x ∧ x.b + x.c = 1 + 3*e

def Realizes (k : ℕ) (f : Entry) : Prop :=
  ∀ q, 1 ≤ q → Odd q → Prefix.Run (steps f).toNat (F k q) (nums (eval k q f))

def Valid (k : ℕ) (f : Entry) : Prop := WellFormed k f ∧ Realizes k f

theorem lookup_two (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (e w : ℤ)
    (hx : Sane k x) (hq : 1 ≤ q) (ho : Odd q) (hs : Separated k x s r)
    (he : even_head k x = false) (hv : Valid s (.two y e)) (hw : 0 ≤ w) :
    run (1 + e.toNat) [left k q x, right k q x, w]
      [left k q (next x s r y), right k q (next x s r y) + w] := by
  obtain ⟨⟨he0, hy, hmass⟩, hreal⟩ := hv
  obtain ⟨hQ, hQo, hH⟩ := quotient_spec k q x s r hx hq ho hs
  obtain ⟨hu, hv⟩ := values_nonnegative k q x hx hq
  obtain ⟨hnext, hc⟩ := next_sane k x s r y hx hs hy
  obtain ⟨hu', hv'⟩ := values_nonnegative k q _ hnext hq
  obtain ⟨hU, hV⟩ := values_nonnegative s (quotient k q x s r) y hy.1 (by omega)
  have hreal' := hreal (quotient k q x s r) (by omega) hQo
  have HR := next_right k q x s r y hx hq ho hs hy
  have hrun := odd_lookup (left k q x) (right k q x) w s (quotient k q x s r) [] e.toNat
    [left s (quotient k q x s r) y] (right s (quotient k q x s r) y) (by omega) hv hw
    (left_odd k q x (by have := hs.2.1; omega) (odd_head_spec k x s r hs he)) hs.1 hQ hQo hH
    hreal' hV (by omega)
  have heq : [left k q (next x s r y), right k q (next x s r y) + w] =
      ([left s (quotient k q x s r) y] ++
        [right s (quotient k q x s r) y + w - right k q x - 1]) ++ [] := by
    rw [next_left k q x s r y hs hy]; simp; omega
  rw [heq]; exact hrun

theorem lookup_one (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r v e w : ℤ)
    (hx : Sane k x) (hq : 1 ≤ q) (ho : Odd q) (hs : Separated k x s r)
    (he : even_head k x = false) (hv : Valid s (.one v e)) (hw : 0 ≤ w) :
    run (1 + e.toNat) [left k q x, right k q x, w] [2^k*q + x.b + x.c + v + 2 + w] := by
  obtain ⟨⟨he0, hve⟩, hreal⟩ := hv
  obtain ⟨hQ, hQo, hH⟩ := quotient_spec k q x s r hx hq ho hs
  obtain ⟨hu, hright⟩ := values_nonnegative k q x hx hq
  have hsum := values_sum k q x
  have hreal' := hreal (quotient k q x s r) (by omega) hQo
  have hsp : (0:ℤ) < 2^s := by positivity
  have hrun := odd_lookup (left k q x) (right k q x) w s (quotient k q x s r) [] e.toNat
    [] (2^s*quotient k q x s r + v) (by omega) hright hw
    (left_odd k q x (by have := hs.2.1; omega) (odd_head_spec k x s r hs he)) hs.1 hQ hQo hH
    hreal' (by nlinarith) (by nlinarith)
  have heq : [2^k*q + x.b + x.c + v + 2 + w] =
      ([] ++ [2^s*quotient k q x s r + v + w - right k q x - 1]) ++ [] := by
    simp; linarith
  rw [heq]; exact hrun

theorem snoc (k : ℕ) (q : ℤ) (hq : 0 ≤ q) : F (k+1) q = F k q ++ nums [2^k*q] := by
  simp only [F, nums, Prefix.F_snoc, List.map_cons, List.map_nil]
  congr 2
  have : (((2:ℤ)^k*q).toNat : ℤ) = ((2^k*q.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by positivity)]; push_cast; rw [Int.toNat_of_nonneg hq]
  exact_mod_cast this.symm

theorem realizes_append (k : ℕ) (f : Entry) (q : ℤ) (h : Realizes k f) (hq : 1 ≤ q)
    (ho : Odd q) :
    Prefix.Run (steps f).toNat (F (k+1) q) (nums (eval k q f ++ [2^k*q])) := by
  rw [snoc k q (by omega)]
  simp only [nums, List.map_append] at h ⊢
  exact (h q hq ho).app _

theorem valid_root : Valid 0 (.one 1 0) := by
  refine ⟨by simp [WellFormed], fun q hq _ ↦ ?_⟩
  simp only [steps, F, eval, nums, Prefix.F, Prefix.geometric, List.map_cons, List.map_nil]
  have : ((2:ℤ)^0*q + 1).toNat = q.toNat + 1 := by simp; omega
  rw [this]
  exact Prefix.Run.refl _

theorem valid_add_one (k : ℕ) (v e : ℤ) (hv : Valid k (.one v e)) :
    Valid (k+1) (.two ⟨1, 1, v, 0⟩ e) := by
  obtain ⟨⟨he, hve⟩, hreal⟩ := hv
  refine ⟨⟨he, ⟨⟨by simp, by simp, by simp, by simp, by simp; omega, by simp⟩,
    by simp, by simp⟩, by simp; omega⟩, fun q hq ho ↦ ?_⟩
  have H := realizes_append k (.one v e) q hreal hq ho
  have heq : eval (k+1) q (.two ⟨1, 1, v, 0⟩ e) = [2^k*q + v, 2^k*q] := by
    simp only [eval, values, left, right, coefficient, Nat.add_sub_cancel, pow_succ]
    congr 2 <;> ring
  rw [heq]; exact H

theorem valid_add_even (k : ℕ) (x : Pair) (e : ℤ) (hv : Valid k (.two x e))
    (heven : even_head k x = true) : Valid (k+1) (.one (x.b + x.c + 3) (e+1)) := by
  obtain ⟨⟨he, hx, hmass⟩, hreal⟩ := hv
  refine ⟨⟨by omega, by omega⟩, fun q hq ho ↦ ?_⟩
  have H := realizes_append k (.two x e) q hreal hq ho
  obtain ⟨hu, hv⟩ := values_nonnegative k q x hx.1 hq
  have HP : (0:ℤ) < 2^k := by positivity
  have hr := run_even (left k q x) (right k q x) (2^k*q) [] (by omega) hv (by positivity)
    (even_head_spec k q x hx.1 ho heven)
  have hrun := H.trans hr
  have hs : (steps (.one (x.b + x.c + 3) (e+1))).toNat = (steps (.two x e)).toNat + 1 := by
    simp only [steps]; omega
  have heq : eval (k+1) q (.one (x.b + x.c + 3) (e+1)) =
      [left k q x + right k q x + 2^k*q + 3] ++ [] := by
    simp only [eval, values_sum, pow_succ, List.append_nil]; congr 1; ring
  rw [hs, heq]; exact hrun

theorem valid_add_lookup_one (k : ℕ) (x : Pair) (e : ℤ) (s : ℕ) (r v f : ℤ)
    (hv : Valid k (.two x e)) (hs : Separated k x s r) (ho : even_head k x = false)
    (hsmall : Valid s (.one v f)) :
    Valid (k+1) (.one (x.b + x.c + v + 2) (e+1+f)) := by
  obtain ⟨⟨he, hx, hmass⟩, hreal⟩ := hv
  obtain ⟨hf, hvf⟩ := hsmall.1
  refine ⟨⟨by omega, by omega⟩, fun q hq hqo ↦ ?_⟩
  have H := realizes_append k (.two x e) q hreal hq hqo
  have HP : (0:ℤ) < 2^k := by positivity
  have hr := lookup_one k q x s r v f (2^k*q) hx.1 hq hqo hs ho hsmall (by positivity)
  have hrun := H.trans hr
  have hst : (steps (.one (x.b + x.c + v + 2) (e+1+f))).toNat =
      (steps (.two x e)).toNat + (1 + f.toNat) := by
    simp only [steps]; omega
  have heq : eval (k+1) q (.one (x.b + x.c + v + 2) (e+1+f)) =
      [2^k*q + x.b + x.c + v + 2 + 2^k*q] := by
    simp only [eval, pow_succ]; congr 1; ring
  rw [hst, heq]
  exact hrun

theorem valid_add_lookup_two (k : ℕ) (x : Pair) (e : ℤ) (s : ℕ) (r : ℤ) (y : Pair) (f : ℤ)
    (hv : Valid k (.two x e)) (hs : Separated k x s r) (ho : even_head k x = false)
    (hsmall : Valid s (.two y f)) :
    Valid (k+1) (.two (widen (next x s r y)) (e+1+f)) := by
  obtain ⟨⟨he, hx, hmass⟩, hreal⟩ := hv
  obtain ⟨hf, hy, hmass'⟩ := hsmall.1
  obtain ⟨hnext, hc⟩ := next_sane k x s r y hx.1 hs hy
  refine ⟨⟨by omega, widen_table k _ hnext (by omega), ?_⟩, fun q hq hqo ↦ ?_⟩
  · have := next_mass x s r y
    simp only [widen]; omega
  · have H := realizes_append k (.two x e) q hreal hq hqo
    have HP : (0:ℤ) < 2^k := by positivity
    have hr := lookup_two k q x s r y f (2^k*q) hx.1 hq hqo hs ho hsmall (by positivity)
    have hrun := H.trans hr
    have hst : (steps (.two (widen (next x s r y)) (e+1+f))).toNat =
        (steps (.two x e)).toNat + (1 + f.toNat) := by
      simp only [steps]; omega
    rw [hst]
    simp only [eval, widen_values]
    exact hrun

/-- The recursive table, recording the actual dependencies including strict separation. -/
inductive Built : ℕ → Entry → Prop
  | root : Built 0 (.one 1 0)
  | one {k v e} : Built k (.one v e) → Built (k+1) (.two ⟨1, 1, v, 0⟩ e)
  | even {k x e} : Built k (.two x e) → even_head k x = true →
      Built (k+1) (.one (x.b + x.c + 3) (e+1))
  | lookup_one {k x e s r v f} : Built k (.two x e) → Separated k x s r →
      even_head k x = false → Built s (.one v f) →
      Built (k+1) (.one (x.b + x.c + v + 2) (e+1+f))
  | lookup_two {k x e s r y f} : Built k (.two x e) → Separated k x s r →
      even_head k x = false → Built s (.two y f) →
      Built (k+1) (.two (widen (next x s r y)) (e+1+f))

theorem built_valid {k f} (h : Built k f) : Valid k f := by
  induction h with
  | root => exact valid_root
  | one _ ih => exact valid_add_one _ _ _ ih
  | even _ he ih => exact valid_add_even _ _ _ ih he
  | lookup_one _ hs ho _ ih ih' => exact valid_add_lookup_one _ _ _ _ _ _ _ ih hs ho ih'
  | lookup_two _ hs ho _ ih ih' => exact valid_add_lookup_two _ _ _ _ _ _ _ ih hs ho ih'


inductive Boundary (lib : ℕ → Entry → Prop) (k : ℕ) : Pair → ℤ → ℕ → Prop
  | even {x} : even_head k x = true → Boundary lib k x 1 1
  | one {x s r v e} : Separated k x s r → even_head k x = false → lib s (.one v e) →
      Boundary lib k x (1+e) 1
  | two {x s r y e f n} : Separated k x s r → even_head k x = false → lib s (.two y e) →
      Boundary lib k (next x s r y) f n → Boundary lib k x (1+e+f) (1+n)

theorem pair_depth (k : ℕ) (x : Pair) (hx : Sane k x) : 1 ≤ x.d := by
  obtain ⟨-, hp, hp2, -⟩ := hx
  rcases Nat.eq_zero_or_pos x.d with h | h
  · rw [h] at hp2; simp at hp2; omega
  · exact h

theorem run_zero (e : ℕ) (xs ys : List ℤ) (h : run e (xs ++ [0]) ys) : exec e xs ys := by
  simp only [run, exec, nums, List.map_append, List.map_cons, List.map_nil] at h ⊢
  exact Prefix.Exec.zero (by simpa using h.exec)

theorem boundary_spec (lib : ℕ → Entry → Prop) (k : ℕ) (x : Pair) (e : ℤ) (n : ℕ)
    (hlib : ∀ s f, lib s f → Valid s f) (h : Boundary lib k x e n) (hx : Sane k x) :
    0 ≤ e ∧ n + x.d ≤ k + 1 ∧
      ∀ q, 1 ≤ q → Odd q → exec e.toNat (values k q x) [2^k*q + x.b + x.c + 3*e] := by
  induction h with
  | @even x he =>
      refine ⟨by omega, by have := hx.1; omega, fun q hq hqo ↦ ?_⟩
      obtain ⟨hu, hv⟩ := values_nonnegative k q x hx hq
      have hr := run_even (left k q x) (right k q x) 0 [] (by omega) hv le_rfl
        (even_head_spec k q x hx hqo he)
      apply run_zero
      have heq : [2^k*q + x.b + x.c + 3*1] = [left k q x + right k q x + 0 + 3] := by
        rw [values_sum]; ring_nf
      rw [heq]; simpa [values] using hr
  | @one x s r v e hs ho hsmall =>
      have hl := hlib _ _ hsmall
      obtain ⟨he, hv⟩ := hl.1
      refine ⟨by omega, by have := hx.1; omega, fun q hq hqo ↦ ?_⟩
      have hr := lookup_one k q x s r v e 0 hx hq hqo hs ho hl le_rfl
      have heq : [2^k*q + x.b + x.c + 3*(1+e)] = [2^k*q + x.b + x.c + v + 2 + 0] := by
        rw [hv]; ring_nf
      rw [heq, show (1+e).toNat = 1 + e.toNat by omega]
      exact run_zero _ _ _ (by simpa [values] using hr)
  | @two x s r y e f n hs ho hsmall _ ih =>
      have hl := hlib _ _ hsmall
      obtain ⟨he, hy, hmass⟩ := hl.1
      obtain ⟨hnext, hc⟩ := next_sane k x s r y hx hs hy
      obtain ⟨hf, hdepth, hexec⟩ := ih hnext
      refine ⟨by omega, ?_, fun q hq hqo ↦ ?_⟩
      · have := pair_depth s y hy.1
        simp only [next] at hdepth; omega
      · have hr := lookup_two k q x s r y e 0 hx hq hqo hs ho hl le_rfl
        rw [add_zero] at hr
        have hr' := run_zero _ (values k q x) _ (by simpa [values] using hr)
        have hrun := Prefix.Exec.trans hr' (hexec q hq hqo)
        have hm := next_mass x s r y
        have heq : [2^k*q + x.b + x.c + 3*(1+e+f)] =
            [2^k*q + (next x s r y).b + (next x s r y).c + 3*f] := by
          congr 1; linarith
        rw [heq, show (1+e+f).toNat = 1 + e.toNat + f.toNat by omega]
        exact hrun

def lower (x : Pair) : Pair := ⟨x.p, x.d, x.b, x.c - 1⟩

theorem lower_sane (k : ℕ) (x : Pair) (h : TablePair k x) : Sane k (lower x) := by
  obtain ⟨⟨hd, hp, hp2, ho, hb, -⟩, -, hc⟩ := h
  exact ⟨hd, hp, hp2, ho, hb, by simp [lower]; omega⟩

theorem lower_values (k : ℕ) (q : ℤ) (x : Pair) :
    values k q (lower x) = [left k q x, right k q x - 1] := by
  simp only [values, lower, left, right, coefficient]; congr 2; ring

theorem last_minus (e k : ℕ) (q : ℤ) (ys : List ℤ) (z : ℤ) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hz : 1 ≤ z) (h : Prefix.Run e (F k q) (nums (ys ++ [z]))) :
    Prefix.Run e (G k q) (nums (ys ++ [z-1])) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k-1, by omega⟩
  simp only [F, G, nums, List.map_append, List.map_cons, List.map_nil] at h ⊢
  rw [show z.toNat = 1 + (z-1).toNat by omega] at h
  exact Prefix.F_to_G e k' q.toNat _ _ (by omega) h

theorem G_single (k : ℕ) (v e : ℤ) (hv : Valid k (.one v e)) (hk : 1 ≤ k) (q : ℤ) (hq : 1 ≤ q)
    (ho : Odd q) : Prefix.Run e.toNat (G k q) (nums [2^k*q + v - 1]) := by
  obtain ⟨⟨he, hve⟩, hr⟩ := hv
  have hP : (0:ℤ) < 2^k := by positivity
  exact last_minus e.toNat k q [] (2^k*q + v) hk hq (by nlinarith) (hr q hq ho)

theorem G_pair (k : ℕ) (x : Pair) (e : ℤ) (hv : Valid k (.two x e)) (hk : 1 ≤ k) (q : ℤ)
    (hq : 1 ≤ q) (ho : Odd q) :
    Prefix.Run e.toNat (G k q) (nums (values k q (lower x))) := by
  obtain ⟨⟨he, hx, hmass⟩, hr⟩ := hv
  rw [lower_values]
  have hcoeff := coefficient_bounds k x hx.1
  have hright : 1 ≤ right k q x := by
    simp only [right]; nlinarith [hx.2.2]
  exact last_minus e.toNat k q [left k q x] (right k q x) hk hq hright (hr q hq ho)

def Returns (lib : ℕ → Entry → Prop) (k : ℕ) : Entry → Prop
  | .one _ _ => True
  | .two x _ => ∃ e n, Boundary lib k (lower x) e n

theorem G_returns (lib : ℕ → Entry → Prop) (k : ℕ) (f : Entry)
    (hlib : ∀ s g, lib s g → Valid s g) (hvalid : Valid k f) (hr : Returns lib k f) (hk : 1 ≤ k)
    (q : ℤ) (hq : 1 ≤ q) (ho : Odd q) : ∃ e m, Prefix.Exec e (G k q) [m] := by
  cases f with
  | one v e =>
      exact ⟨e.toNat, (2^k*q + v - 1).toNat, (G_single k v e hvalid hk q hq ho).exec⟩
  | two x e =>
      obtain ⟨f, n, hb⟩ := hr
      obtain ⟨hf, hn, hexec⟩ := boundary_spec lib k (lower x) f n hlib hb
        (lower_sane k x hvalid.1.2.1)
      exact ⟨e.toNat + f.toNat, _, (G_pair k x e hvalid hk q hq ho).exec.trans (hexec q hq ho)⟩

end BMO9.Table
