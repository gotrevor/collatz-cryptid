/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.UniqueTable

/-!
# BMO #9, port of Rocq `Module CheckTable` (BMO9.v lines 1191-1396, ccz181078)

A computable builder for the table, checked by evaluation for `1 ≤ k ≤ 65536`.
-/

namespace BMO9.CheckTable

open Table

/-- `n = 2^s * r` with `r` odd (for `n > 0`). -/
def split2 (n : ℕ) : ℕ × ℕ :=
  if h : n ≠ 0 ∧ n % 2 = 0 then
    let sr := split2 (n / 2)
    (sr.1 + 1, sr.2)
  else (0, n)
termination_by n
decreasing_by omega

def separate (k : ℕ) (x : Pair) : Option (ℕ × ℤ) :=
  let sr := split2 (h x).toNat
  if 1 ≤ sr.1 ∧ sr.1 + x.d < k ∧ h x = 2^sr.1 * (sr.2 : ℤ) ∧ (sr.2 : ℤ) % 2 = 1 then
    some (sr.1, sr.2)
  else none

theorem separate_spec (k : ℕ) (x : Pair) (s : ℕ) (r : ℤ) (h : separate k x = some (s, r)) :
    Separated k x s r := by
  unfold separate at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hc.1, hc.2.1, hc.2.2.1, Int.odd_iff.2 hc.2.2.2⟩

def advance (lookup : ℕ → Option Entry) (k : ℕ) : Entry → Option Entry
  | .one v e => some (.two ⟨1, 1, v, 0⟩ e)
  | .two x e =>
      if even_head k x then some (.one (x.b + x.c + 3) (e+1)) else
      match separate k x with
      | some (s, r) =>
          match lookup s with
          | some (.one v f) => some (.one (x.b + x.c + v + 2) (e+1+f))
          | some (.two y f) => some (.two (widen (next x s r y)) (e+1+f))
          | none => none
      | none => none

theorem advance_spec (lookup : ℕ → Option Entry) (k : ℕ) (f g : Entry)
    (hlib : ∀ s x, lookup s = some x → Built s x) (hf : Built k f)
    (h : advance lookup k f = some g) : Built (k+1) g := by
  cases f with
  | one v e =>
      simp only [advance, Option.some.injEq] at h; subst h; exact Built.one hf
  | two x e =>
      simp only [advance] at h
      split_ifs at h with he
      · simp only [Option.some.injEq] at h; subst h; exact Built.even hf he
      · have he' : even_head k x = false := by simpa using he
        split at h
        · rename_i s r hs
          have hsep := separate_spec k x s r hs
          split at h
          · rename_i v f hl
            simp only [Option.some.injEq] at h; subst h
            exact Built.lookup_one hf hsep he' (hlib _ _ hl)
          · rename_i y f hl
            simp only [Option.some.injEq] at h; subst h
            exact Built.lookup_two hf hsep he' (hlib _ _ hl)
          · exact absurd h (by simp)
        · exact absurd h (by simp)

def finish (lookup : ℕ → Option Entry) (k : ℕ) : ℕ → Pair → Option (ℤ × ℕ)
  | 0, _ => none
  | fuel+1, x =>
      if even_head k x then some (1, 1) else
      match separate k x with
      | some (s, r) =>
          match lookup s with
          | some (.one _ e) => some (1+e, 1)
          | some (.two y e) =>
              match finish lookup k fuel (next x s r y) with
              | some (f, n) => some (1+e+f, 1+n)
              | none => none
          | none => none
      | none => none

theorem finish_spec (lookup : ℕ → Option Entry) (k : ℕ)
    (hlib : ∀ s f, lookup s = some f → Built s f) :
    ∀ fuel x e n, finish lookup k fuel x = some (e, n) → Boundary Built k x e n := by
  intro fuel
  induction fuel with
  | zero => intro x e n h; simp [finish] at h
  | succ fuel ih =>
      intro x e n h
      simp only [finish] at h
      split_ifs at h with he
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact Boundary.even he
      · have he' : even_head k x = false := by simpa using he
        split at h
        · rename_i s r hs
          have hsep := separate_spec k x s r hs
          split at h
          · rename_i v f hl
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Boundary.one hsep he' (hlib _ _ hl)
          · rename_i y f hl
            split at h
            · rename_i g m ht
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Boundary.two hsep he' (hlib _ _ hl) (ih _ _ _ ht)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)

def return_check (lookup : ℕ → Option Entry) (k : ℕ) : Entry → Bool
  | .one _ _ => true
  | .two x _ => (finish lookup k 64 (lower x)).isSome

theorem return_check_spec (lookup : ℕ → Option Entry) (k : ℕ) (f : Entry)
    (hlib : ∀ s g, lookup s = some g → Built s g) (h : return_check lookup k f = true) :
    Returns Built k f := by
  cases f with
  | one => trivial
  | two x e =>
      simp only [return_check, Option.isSome_iff_exists] at h
      obtain ⟨⟨f, n⟩, hf⟩ := h
      exact ⟨f, n, finish_spec lookup k hlib _ _ _ _ hf⟩

def lookup (bank : List Entry) (s : ℕ) : Option Entry := bank[s]?

def BankOk (bank : List Entry) : Prop := ∀ i f, bank[i]? = some f → Built i f

theorem bank_snoc (bank : List Entry) (f : Entry) (hb : BankOk bank)
    (hf : Built bank.length f) : BankOk (bank ++ [f]) := by
  intro i g hg
  rcases lt_or_ge i bank.length with hi | hi
  · rw [List.getElem?_append_left hi] at hg; exact hb _ _ hg
  · rw [List.getElem?_append_right hi] at hg
    rcases Nat.lt_or_ge (i - bank.length) 1 with h | h
    · rw [show i - bank.length = 0 by omega] at hg
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg; rwa [show i = bank.length by omega]
    · rw [List.getElem?_eq_none (by simp; omega)] at hg; cases hg

def bank_build : ℕ → Option (List Entry)
  | 0 => some [.one 1 0]
  | n+1 =>
      match bank_build n with
      | some bank =>
          match bank[n]? with
          | some f =>
              match advance (lookup bank) n f with
              | some g => some (bank ++ [g])
              | none => none
          | none => none
      | none => none

theorem bank_build_spec : ∀ n bank, bank_build n = some bank →
    bank.length = n + 1 ∧ BankOk bank := by
  intro n
  induction n with
  | zero =>
      intro bank h
      simp only [bank_build, Option.some.injEq] at h; subst h
      refine ⟨rfl, fun i f hf ↦ ?_⟩
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf; exact Built.root
      · simp at hf
  | succ n ih =>
      intro bank h
      simp only [bank_build] at h
      split at h
      · rename_i xs hxs
        obtain ⟨hlen, hbank⟩ := ih xs hxs
        split at h
        · rename_i f hf
          split at h
          · rename_i g hg
            simp only [Option.some.injEq] at h; subst h
            refine ⟨by simp [hlen], bank_snoc _ _ hbank ?_⟩
            rw [hlen]
            exact advance_spec _ _ _ _ (fun s x hx ↦ hbank _ _ hx) (hbank _ _ hf) hg
          · cases h
        · cases h
      · cases h

def depth : Entry → ℕ
  | .one _ _ => 0
  | .two x _ => x.d

/-- Rocq `Z.log2_up k`. -/
def log2up (k : ℕ) : ℕ := Nat.clog 2 k

def Bounded (k : ℕ) (f : Entry) : Prop :=
  steps f ≤ 4*(k:ℤ)^3 ∧ depth f ≤ 6*log2up k + 9

def bounds_check (k : ℕ) (f : Entry) : Bool :=
  decide (steps f ≤ 4*(k:ℤ)^3) && decide (depth f ≤ 6*log2up k + 9)

theorem bounds_check_spec (k : ℕ) (f : Entry) (h : bounds_check k f = true) : Bounded k f := by
  simpa [bounds_check, Bounded] using h

def check (bank : List Entry) : ℕ → ℕ → Entry → Bool
  | 0, _, _ => true
  | fuel+1, k, f =>
      if bounds_check k f && return_check (lookup bank) k f then
        match advance (lookup bank) k f with
        | some g => check bank fuel (k+1) g
        | none => false
      else false

theorem check_spec (bank : List Entry) (hbank : BankOk bank) :
    ∀ fuel k f, Built k f → check bank fuel k f = true →
      ∀ j, k ≤ j → j < k + fuel → ∃ g, Built j g ∧ Bounded j g ∧ Returns Built j g := by
  intro fuel
  induction fuel with
  | zero => intro k f _ _ j h1 h2; omega
  | succ fuel ih =>
      intro k f hf hc j hj1 hj2
      simp only [check] at hc
      split_ifs at hc with hgood
      simp only [Bool.and_eq_true] at hgood
      split at hc
      · rename_i g hg
        rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
        · exact ⟨f, hf, bounds_check_spec _ _ hgood.1,
            return_check_spec _ _ _ (fun s g hs ↦ hbank _ _ hs) hgood.2⟩
        · exact ih (k+1) g (advance_spec _ _ _ _ (fun s x hx ↦ hbank _ _ hx) hf hg) hc j
            (by omega) (by omega)
      · cases hc

def bank : List Entry := (bank_build 128).getD []

theorem bank_checked : bank_build 128 = some bank := by native_decide

theorem checked_bank : BankOk bank := (bank_build_spec _ _ bank_checked).2

theorem first : Built 1 (.two ⟨1, 1, 1, 0⟩ 0) := Built.one Built.root

theorem finite_check : check bank 65536 1 (.two ⟨1, 1, 1, 0⟩ 0) = true := by native_decide

theorem base_structured (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 65536) :
    ∃ f, Built k f ∧ Bounded k f ∧ Returns Built k f :=
  check_spec bank checked_bank 65536 1 _ first finite_check k h1 (by omega)

theorem P16 : Built 16 (.one 37 12) := checked_bank 16 _ (by native_decide)

end BMO9.CheckTable
