/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem9.Prefix

/-!
# BMO #9: from compressed prefix steps to the published stream rules

`Prefix.Step` compresses runs of the published rules.  This file shows that a stream sequence
following the published recursion simulates every `Prefix.Exec`, never passing a halting prefix,
and derives the headline's conclusion from the singleton-return statement.
-/

namespace BMO9.Bridge

open Prefix

/-- One application of the published rules (the right side of `x_rec`). -/
def R (s : ℕ → ℕ) : ℕ → ℕ :=
  if s 0 = 0 then
    fun i ↦ if i = 0 then 3 + s 1 + s 2 else s (i + 2)
  else if s 0 = 1 then
    fun i ↦ if i = 0 then s 1 - 1 else if i = 1 then 0 else if i = 2 then 1
      else if i = 3 then 1 + s 2 else s (i - 1)
  else
    fun i ↦ if i = 0 then s 0 - 2 else if i ≤ 2 then 1 + s i else s i

/-- The stream denoted by a finite prefix. -/
def stream (xs : List ℕ) (i : ℕ) : ℕ := xs.getD i 0

def Safe (s : ℕ → ℕ) : Prop := ¬ (s 0 = 1 ∧ s 1 = 0)

theorem stream_zero (xs : List ℕ) : stream (xs ++ [0]) = stream xs := by
  funext i
  simp only [stream, List.getD_eq_getElem?_getD]
  rcases lt_or_ge i xs.length with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right h, List.getElem?_eq_none h]
    rcases Nat.lt_or_ge (i - xs.length) 1 with h' | h'
    · simp [show i - xs.length = 0 by omega]
    · rw [List.getElem?_eq_none (by simp; omega)]

theorem R_two (s : ℕ → ℕ) (h : 2 ≤ s 0) :
    R s = fun i ↦ if i = 0 then s 0 - 2 else if i ≤ 2 then 1 + s i else s i := by
  simp only [R, if_neg (show s 0 ≠ 0 by omega), if_neg (show s 0 ≠ 1 by omega)]

section
variable (x : ℕ → ℕ → ℕ) (hx : ∀ n, x (n + 1) = R (x n))
include hx

theorem iter (N n c : ℕ) (hs : x N 0 = 2*n + c) :
    ∀ k ≤ n, x (N+k) = fun i ↦ if i = 0 then 2*(n-k) + c else if i ≤ 2 then k + x N i
      else x N i := by
  intro k hk
  induction k with
  | zero =>
      funext i; split_ifs with h <;> simp_all
  | succ k ih =>
      rw [← Nat.add_assoc, hx, ih (by omega), R_two _ (by simp; omega)]
      funext i; split_ifs <;> omega

theorem sim_step {e xs ys} (h : Step e xs ys) (N : ℕ) (hN : x N = stream xs) :
    ∃ d, 1 ≤ d ∧ x (N+d) = stream ys ∧ ∀ i < d, Safe (x (N+i)) := by
  cases h with
  | E n v w r =>
      have hs : x N 0 = 2*n + 0 := by simp [hN, stream]
      have hit := iter x hx N n 0 hs
      refine ⟨n+1, by omega, ?_, ?_⟩
      · rw [← Nat.add_assoc, hx, hit n le_rfl]
        simp only [R, Nat.sub_self, mul_zero, add_zero, if_true, if_false,
          OfNat.ofNat_ne_zero, show ¬ (1 = 0) from by omega, show (1:ℕ) ≤ 2 by omega,
          show (2:ℕ) ≤ 2 by omega]
        funext i; rcases i with _ | i
        · simp [hN, stream]; ring
        · simp [hN, stream]
      · intro i hi
        rw [hit i (by omega)]
        simp only [Safe, if_true]; omega
  | O n v w r hnv =>
      have hs : x N 0 = 2*n + 1 := by simp [hN, stream]
      have hit := iter x hx N n 1 hs
      refine ⟨n+1, by omega, ?_, ?_⟩
      · rw [← Nat.add_assoc, hx, hit n le_rfl]
        simp only [R, Nat.sub_self, mul_zero, zero_add, if_true, if_false,
          show (1:ℕ) ≤ 2 by omega, show ¬ (1 = 0) from by omega]
        funext i; rcases i with _ | _ | _ | _ | i
        · simp [hN, stream]
        · rfl
        · rfl
        · simp [hN, stream]; ring
        · simp [hN, stream]
      · intro i hi
        rw [hit i (by omega)]
        simp only [Safe, if_true, show (1:ℕ) ≤ 2 by omega]
        simp [hN, stream]; omega

theorem sim_exec {e xs ys} (h : Exec e xs ys) :
    ∀ N, x N = stream xs → ∃ d, e ≤ d ∧ x (N+d) = stream ys ∧ ∀ i < d, Safe (x (N+i)) := by
  induction h with
  | stop xs => intro N hN; exact ⟨0, le_rfl, by simpa using hN, by simp⟩
  | @take e f xs ys zs hs _ ih =>
      intro N hN
      obtain ⟨d1, hd1, h1, s1⟩ := sim_step x hx hs N hN
      obtain ⟨d2, hd2, h2, s2⟩ := ih (N+d1) h1
      have he : e ≤ 1 := by cases hs <;> omega
      refine ⟨d1+d2, by omega, by rwa [← Nat.add_assoc], ?_⟩
      intro i hi
      rcases lt_or_ge i d1 with h | h
      · exact s1 i h
      · have := s2 (i - d1) (by omega)
        rwa [Nat.add_assoc, Nat.add_sub_cancel' h] at this
  | zero _ ih =>
      intro N hN
      exact ih N (by rw [stream_zero]; exact hN)

theorem forever (hx0 : x 0 = fun _ ↦ 0)
    (core : ∀ j, ∃ e m, Exec (1+e) [3*j] [m]) :
    ∀ n, Safe (x n) := by
  have key : ∀ K, ∃ N, K ≤ N ∧ ∃ j, x N = stream [3*j] ∧ ∀ i < N, Safe (x i) := by
    intro K
    induction K with
    | zero =>
        refine ⟨0, le_rfl, 0, ?_, by simp⟩
        rw [hx0]; funext i; rcases i with _ | i <;> simp [stream]
    | succ K ih =>
        obtain ⟨N, hN, j, hj, hs⟩ := ih
        obtain ⟨e, m, he⟩ := core j
        obtain ⟨d, hd, h1, s1⟩ := sim_exec x hx he N hj
        have hm := he.mass_eq
        simp [mass] at hm
        refine ⟨N+d, by omega, j+1+e, by rw [h1]; congr 3; omega, ?_⟩
        intro i hi
        rcases lt_or_ge i N with h | h
        · exact hs i h
        · have := s1 (i - N) (by omega)
          rwa [Nat.add_sub_cancel' h] at this
  intro n
  obtain ⟨N, hN, _, _, hs⟩ := key (n+1)
  exact hs n (by omega)

end

end BMO9.Bridge
