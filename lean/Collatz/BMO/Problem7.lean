/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Beaver Math Olympiad problem 7: every term is odd

BMO#7 is the mathematical reformulation of the non-halting of the 6-state Turing machine
`1RB1RF_1RC0RA_1LD1RC_1LE0LE_0RA0LD_0RB---` from the all-0 tape.

Let `f n = n + 1 + (v₂(n+1) mod 2)`, `a 0 = 1` and `a (n+1) = f^[n+2] (a n / 2)`.
Does some `a k` turn out even?  No.

## The mechanism

`f n` is `n + 2` when `v₂(n+1)` is odd and `n + 1` otherwise.  So `f` climbs one step at a time
and skips the integers with odd 2-adic valuation.  Put `b n = a n - 1`.  Call `k` *higheven*
when `v₂ k ≥ 4` and `v₂ k` is even.  For `n ≥ 3`, the terms `b n` list, in increasing order, the
`k` with `v₂ k = 1`, or `k` higheven, or `k > 4` with `k - 4` higheven.  All of these are even.

*References:*

- [Beaver Math Olympiad wiki page](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) (§7)
- The ansatz is due to bbchallenge contributor planet246 (2025-09-30).  The proof by induction
  from it is by pomme_de_terre (2025-10-24), posted in the bbchallenge Discord:
  <https://discord.com/channels/960643023006490684/1421782442213376000/1431483206208852001>
-/

namespace Collatz.BMO.Problem7

/-! ## Sanity anchors -/

/-- The step function, as an executable definition. -/
def f (n : ℕ) : ℕ := n + 1 + padicValNat 2 (n + 1) % 2

/-- The BMO#7 sequence, as an executable definition. -/
def seq : ℕ → ℕ
  | 0 => 1
  | n + 1 => f^[n + 2] (seq n / 2)

/-- The first terms match the machine's orbit as posted by mxdys (2025-09-28):
`(0,1) → (1,3) → (2,5) → (3,7) → (4,11) → (5,15) → …`. -/
example : (List.range 6).map seq = [1, 3, 5, 7, 11, 15] := by decide +kernel

/-! ## The proof

We track `b n = seq n - 1`.  From `n = 3` on, consecutive terms `(p, next p)` of `S` give
consecutive `b`'s (`inv`), and `step` carries the pair forward.  `S` holds only even numbers. -/

local notation "v" => padicValNat 2

lemma vcase (x : ℕ) : (x = 0 ∧ v x = 0) ∨ (x % 2 = 1 ∧ v x = 0) ∨ (x % 4 = 2 ∧ v x = 1) ∨
    (x % 8 = 4 ∧ v x = 2) ∨ (x % 16 = 8 ∧ v x = 3) ∨ (x % 16 = 0 ∧ x ≠ 0 ∧ 4 ≤ v x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 := padicValNat_dvd_iff_le (p := 2) (n := 1) hx
  have h2 := padicValNat_dvd_iff_le (p := 2) (n := 2) hx
  have h3 := padicValNat_dvd_iff_le (p := 2) (n := 3) hx
  have h4 := padicValNat_dvd_iff_le (p := 2) (n := 4) hx
  simp only [Nat.dvd_iff_mod_eq_zero] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  omega

lemma vhalf (x : ℕ) (h : x % 2 = 0) : v (x / 2) + 1 = v x ∨ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have := padicValNat.div (p := 2) (b := x) (Nat.dvd_of_mod_eq_zero h)
  rcases vcase x with h' | h' | h' | h' | h' | h' <;> omega

lemma fG (n m : ℕ) (hm : m = n + 1) (h : v m % 2 = 0) : f n = m := by
  subst hm; simp [f, h]

lemma fN (n m : ℕ) (hm : m = n + 2) (h : v (n + 1) % 2 = 1) : f n = m := by
  subst hm; simp [f, h]


/-- `k` is *higheven*: `v₂ k ≥ 4` and `v₂ k` is even. -/
def H (k : ℕ) : Prop := 4 ≤ v k ∧ v k % 2 = 0

instance : DecidablePred H := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The target set (shifted by one): `b n = a n - 1` ranges over it. -/
def S (k : ℕ) : Prop := k % 4 = 2 ∨ H k ∨ H (k - 4)

instance : DecidablePred S := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The successor in `S`. -/
def next (q : ℕ) : ℕ := if q % 4 = 2 ∧ ¬H (q + 2) ∧ ¬H (q - 2) then q + 4 else q + 2

lemma H_mod {k : ℕ} (h : H k) : k % 16 = 0 ∧ k ≠ 0 := by
  unfold H at h; rcases vcase k with h' | h' | h' | h' | h' | h' <;> omega

lemma next_two {q : ℕ} (h : ¬ (q % 4 = 2 ∧ ¬H (q + 2) ∧ ¬H (q - 2))) : next q = q + 2 := by
  simp only [next, if_neg h]

lemma next_four {q : ℕ} (h : q % 4 = 2) (h1 : ¬H (q + 2)) (h2 : ¬H (q - 2)) :
    next q = q + 4 := by
  simp only [next, if_pos (And.intro h (And.intro h1 h2))]

/-- The pair step.  If `q = next p` follows `a N = q + 1 = f^[N+1] (p/2)`, then
`f^[N+2] (q/2)` lands on `next q + 1`: both orbits merge after `j + 1` steps. -/
lemma step (p : ℕ) (hp : S p) :
    ∃ j, f^[j + 1] (p / 2) = f (next p / 2) ∧ f^[j + 1] (next p + 1) = next (next p) + 1 := by
  rcases hp with hp | hp | hp
  · by_cases c1 : H (p + 2)
    · -- B1
      have hm := H_mod c1
      have hq : next p = p + 2 := next_two (by tauto)
      have hq' : next (p + 2) = p + 4 := next_two (by omega)
      rw [hq, hq']
      refine ⟨0, ?_, ?_⟩
      · show f (p / 2) = f ((p + 2) / 2)
        have h2 := vhalf (p + 2) (by omega)
        unfold H at c1
        rw [fN (p / 2) (p / 2 + 2) rfl (by rw [show p / 2 + 1 = (p + 2) / 2 by omega]; omega),
          fG ((p + 2) / 2) (p / 2 + 2) (by omega)
            (by have := vcase (p / 2 + 2); omega)]
      · show f (p + 2 + 1) = p + 4 + 1
        exact fN _ _ rfl (by have := vcase (p + 2 + 1 + 1); omega)
    by_cases c2 : H (p - 2)
    · -- B2
      have hm := H_mod c2
      have hq : next p = p + 2 := next_two (by tauto)
      have hq' : next (p + 2) = p + 4 := next_two (by omega)
      rw [hq, hq']
      refine ⟨0, ?_, ?_⟩
      · show f (p / 2) = f ((p + 2) / 2)
        rw [fN (p / 2) (p / 2 + 2) rfl (by have := vcase (p / 2 + 1); omega),
          fG ((p + 2) / 2) (p / 2 + 2) (by omega)
            (by have := vcase (p / 2 + 2); omega)]
      · show f (p + 2 + 1) = p + 4 + 1
        exact fN _ _ rfl (by have := vcase (p + 2 + 1 + 1); omega)
    -- C
    have hq : next p = p + 4 := next_four hp c1 c2
    rw [hq]
    have e2 := vcase (p + 2)
    unfold H at c1
    by_cases c3 : v (p + 2) = 2
    · -- C1
      refine ⟨1, ?_, ?_⟩
      · show f (f (p / 2)) = f ((p + 4) / 2)
        rw [fN (p / 2) ((p + 4) / 2) (by omega)
          (by rw [show p / 2 + 1 = (p + 2) / 2 by omega]; have := vcase ((p + 2) / 2); omega)]
      · show f (f (p + 4 + 1)) = next (p + 4) + 1
        by_cases c4 : H (p + 6)
        · have hq' : next (p + 4) = p + 6 :=
            next_two (by rw [show p + 4 + 2 = p + 6 by omega]; tauto)
          rw [hq']
          unfold H at c4
          rw [fG (p + 4 + 1) (p + 6) (by omega) (by omega),
            fG (p + 6) (p + 7) (by omega) (by have := vcase (p + 7); omega)]
        · have hq' : next (p + 4) = p + 8 :=
            next_four (by omega) (by rw [show p + 4 + 2 = p + 6 by omega]; exact c4)
              (by rw [show p + 4 - 2 = p + 2 by omega]; unfold H; omega)
          rw [hq']
          unfold H at c4
          have := vcase (p + 6)
          rw [fN (p + 4 + 1) (p + 7) (by omega) (by rw [show p + 4 + 1 + 1 = p + 6 by omega]; omega),
            fN (p + 7) (p + 9) (by omega) (by have := vcase (p + 7 + 1); omega)]
    · -- C2
      have h2 := vhalf (p + 2) (by omega)
      refine ⟨2, ?_, ?_⟩
      · show f (f (f (p / 2))) = f ((p + 4) / 2)
        rw [fG (p / 2) ((p + 2) / 2) (by omega) (by omega),
          fG ((p + 2) / 2) ((p + 4) / 2) (by omega) (by have := vcase ((p + 4) / 2); omega)]
      · show f (f (f (p + 4 + 1))) = next (p + 4) + 1
        have e6 := vcase (p + 6)
        have hq' : next (p + 4) = p + 8 :=
          next_four (by omega) (by rw [show p + 4 + 2 = p + 6 by omega]; unfold H; omega)
            (by rw [show p + 4 - 2 = p + 2 by omega]; unfold H; omega)
        rw [hq', fG (p + 4 + 1) (p + 6) (by omega) (by omega),
          fG (p + 6) (p + 7) (by omega) (by have := vcase (p + 7); omega),
          fN (p + 7) (p + 9) (by omega) (by have := vcase (p + 7 + 1); omega)]
  · -- A1
    have hm := H_mod hp
    have hq : next p = p + 2 := next_two (by omega)
    have hq' : next (p + 2) = p + 4 :=
      next_two (by rw [show p + 2 - 2 = p by omega]; tauto)
    rw [hq, hq']
    refine ⟨1, ?_, ?_⟩
    · show f (f (p / 2)) = f ((p + 2) / 2)
      rw [fG (p / 2) ((p + 2) / 2) (by omega) (by have := vcase ((p + 2) / 2); omega)]
    · show f (f (p + 2 + 1)) = p + 4 + 1
      rw [fG (p + 2 + 1) (p + 4) (by omega) (by have := vcase (p + 4); omega),
        fG (p + 4) (p + 4 + 1) (by omega) (by have := vcase (p + 4 + 1); omega)]
  · -- A2
    have hm := H_mod hp
    have hq : next p = p + 2 := next_two (by omega)
    have hq' : next (p + 2) = p + 6 :=
      next_four (by omega)
        (by rw [show p + 2 + 2 = p + 4 by omega]; unfold H; have := vcase (p + 4); omega)
        (by rw [show p + 2 - 2 = p by omega]; unfold H; have := vcase p; omega)
    rw [hq, hq']
    refine ⟨1, ?_, ?_⟩
    · show f (f (p / 2)) = f ((p + 2) / 2)
      rw [fG (p / 2) ((p + 2) / 2) (by omega) (by have := vcase ((p + 2) / 2); omega)]
    · show f (f (p + 2 + 1)) = p + 6 + 1
      rw [fN (p + 2 + 1) (p + 5) (by omega) (by have := vcase (p + 2 + 1 + 1); omega),
        fN (p + 5) (p + 6 + 1) (by omega) (by have := vcase (p + 5 + 1); omega)]


lemma S_even {p : ℕ} (hp : S p) : p % 2 = 0 := by
  rcases hp with hp | hp | hp
  · omega
  · have := H_mod hp; omega
  · have := H_mod hp; omega

lemma S_next {p : ℕ} (hp : S p) : S (next p) := by
  have he := S_even hp
  unfold next
  split_ifs with h
  · left; omega
  · rcases hp with hp | hp | hp
    · by_cases c1 : H (p + 2)
      · exact Or.inr (Or.inl c1)
      · have c2 : H (p - 2) := by tauto
        exact Or.inr (Or.inr (by rwa [show p + 2 - 4 = p - 2 by have := H_mod c2; omega]))
    · have := H_mod hp; left; omega
    · have := H_mod hp; left; omega

lemma inv (n : ℕ) : ∃ p, S p ∧ f^[n + 5] (p / 2) = next p + 1 ∧ seq (n + 4) = next p + 1 := by
  induction n with
  | zero => exact ⟨6, by decide +kernel, by decide +kernel, by decide +kernel⟩
  | succ n ih =>
    obtain ⟨p, hp, h1, h2⟩ := ih
    obtain ⟨j, hj1, hj2⟩ := step p hp
    have hev : next p % 2 = 0 := S_even (S_next hp)
    have key : f^[n + 6] (next p / 2) = next (next p) + 1 := by
      rw [Function.iterate_succ_apply, ← hj1, ← Function.iterate_add_apply, add_comm,
        Function.iterate_add_apply, h1, hj2]
    refine ⟨next p, S_next hp, key, ?_⟩
    show f^[n + 4 + 2] (seq (n + 4) / 2) = _
    rw [h2, show (next p + 1) / 2 = next p / 2 by omega]
    exact key

theorem seq_odd (n : ℕ) : seq n % 2 = 1 := by
  rcases (show n < 4 ∨ ∃ m, n = m + 4 from
    if h : n < 4 then Or.inl h else Or.inr ⟨n - 4, by omega⟩) with h | ⟨m, rfl⟩
  · interval_cases n <;> decide +kernel
  · obtain ⟨p, hp, -, h⟩ := inv m
    have := S_even (S_next hp)
    omega


/-! ## The headline

Statement in the style of `google-deepmind/formal-conjectures`
`FormalConjectures/Other/BeaverMathOlympiad.lean`, so it can anchor a `formal_proof` link. -/

theorem beaver_math_olympiad_problem_7
    (f : ℕ → ℕ) (hf : f = fun n ↦ n + 1 + padicValNat 2 (n + 1) % 2)
    (a : ℕ → ℕ)
    (a_ini : a 0 = 1)
    (a_rec : ∀ n, a (n + 1) = f^[n + 2] (a n / 2)) :
    ¬ ∃ k, Even (a k) := by
  have ha : a = seq := by
    funext n
    induction n with
    | zero => simp [a_ini, seq]
    | succ n ih => rw [a_rec, ih, hf]; rfl
  rintro ⟨k, hk⟩
  rw [ha, Nat.even_iff] at hk
  have := seq_odd k
  omega

end Collatz.BMO.Problem7
