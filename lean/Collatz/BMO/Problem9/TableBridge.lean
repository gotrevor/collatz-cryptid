/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Block
import Collatz.BMO.Problem9.CheckTable

/-!
# BMO #9, port of Rocq `Module Bridge` and `Module Finite` (BMO9.v lines 1398-1505)

Glue from table pairs to `Block` kernels, and the finite base.  (Renamed `TableBridge`: the
repo's `Bridge` is the stream simulation.)
-/

namespace BMO9.TableBridge

open Table

def kernel (x : Pair) : Block.Kernel := ⟨2^x.d, x.p, x.b, x.b + x.c + 2⟩

theorem kernel_good (s : ℕ) (x : Pair) (h : TablePair s x) : (kernel x).Good := by
  obtain ⟨⟨hd, hp, hp2, ho, hb, hc⟩, hhalf, hc0⟩ := h
  exact ⟨by simp [kernel], hp, hhalf, hb, by simp [kernel]; omega⟩

theorem gain_large (k : ℕ) (f : Entry) (h : Valid k f) : (k:ℤ) < 3*(steps f + 1) := by
  obtain ⟨hwf, hr⟩ := h
  have he : 0 ≤ steps f := by cases f <;> exact hwf.1
  have hl := (hr 1 le_rfl odd_one).length_le
  have hlen : (eval k 1 f).length ≤ 2 := by cases f <;> simp [eval, values]
  simp only [F, Prefix.F, nums, List.length_map, List.length_cons,
    Prefix.geometric_length] at hl
  omega

theorem kernel_gain (s : ℕ) (x : Pair) (e : ℤ) (h : Valid s (.two x e)) :
    (s:ℤ) < (kernel x).gain := by
  have := gain_large _ _ h
  obtain ⟨he, hx, hmass⟩ := h.1
  simp only [kernel, steps] at this ⊢; omega

theorem lookup_leading (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (hx : Sane k x)
    (hq : 1 ≤ q) (ho : Odd q) (hs : Separated k x s r) (hy : TablePair s y) :
    2^y.d*left k q (next x s r y) = y.p*(left k q x + 2*right k q x + 3) + 2^y.d*y.b := by
  have HH := (quotient_spec k q x s r hx hq ho hs).2.2
  rw [← next_left k q x s r y hs hy, HH]
  simp only [left, coefficient]
  rw [pow_split s y.d hy.1.1]; ring

theorem lookup_call (k : ℕ) (q : ℤ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (hx : Sane k x)
    (hq : 1 ≤ q) (ho : Odd q) (hs : Separated k x s r) (hy : TablePair s y) :
    Block.call (kernel y)
      (left k q x + right k q x) (left k q x + 2*right k q x + 3)
      (left k q (next x s r y) + right k q (next x s r y))
      (left k q (next x s r y) + 2*right k q (next x s r y) + 3) := by
  have HL := lookup_leading k q x s r y hx hq ho hs hy
  have HM : left k q (next x s r y) + right k q (next x s r y) =
      left k q x + right k q x + (y.b + y.c + 2) := by
    rw [values_sum, values_sum]; linarith [next_mass x s r y]
  refine ⟨HM, ?_⟩
  simp only [kernel]
  have h2 : 2*right k q (next x s r y) = 2*(left k q x + right k q x + (y.b + y.c + 2)) -
      2*left k q (next x s r y) := by linarith
  rw [show left k q (next x s r y) + 2*right k q (next x s r y) + 3 =
      2*(left k q x + right k q x + (y.b + y.c + 2)) - left k q (next x s r y) + 3 by linarith]
  linear_combination -HL

theorem head_value (k : ℕ) (q : ℤ) (x : Pair) (hx : Sane k x) (hq : Odd q) :
    even_head k x = (left k q x % 2 == 0) := by
  obtain ⟨a, ha⟩ := head_parity k q x hx hq
  rw [ha, even_head]
  have : (head_constant k x + 2*a) % 2 = head_constant k x % 2 := by omega
  rw [this]

theorem lookup_parity (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) (y : Pair) (hx : Sane k x)
    (hs : Separated k x s r) (hy : TablePair s y) :
    even_head k (next x s r y) = even_head s y := by
  obtain ⟨hnext, -⟩ := next_sane k x s r y hx hs hy
  rw [head_value k 1 _ hnext odd_one, ← next_left k 1 x s r y hs hy,
    head_value s (quotient k 1 x s r) y hy.1 (quotient_spec k 1 x s r hx le_rfl odd_one hs).2.1]

/-! ## Rocq `Module Finite` -/

theorem all_base (k : ℕ) (f : Entry) (hk1 : 1 ≤ k) (hk : k ≤ 65536) (hf : Built k f) :
    CheckTable.Bounded k f ∧ Returns Built k f := by
  obtain ⟨g, hg, hr⟩ := CheckTable.base_structured k hk1 hk
  rw [UniqueTable.built_unique hf g hg]; exact hr

theorem G_returns_base (k t : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 65536) :
    ∃ e m, Prefix.Exec e (Prefix.G k (1+2*t)) [m] := by
  obtain ⟨f, hf, -, hr⟩ := CheckTable.base_structured k hk1 hk
  have := Table.G_returns Built k f (fun _ _ h ↦ built_valid h) (built_valid hf) hr hk1
    (1 + 2*(t:ℤ)) (by omega) ⟨t, by ring⟩
  simpa [Table.G, show (1 + 2*(t:ℤ)).toNat = 1 + 2*t by omega] using this

end BMO9.TableBridge
