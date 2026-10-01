/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic

/-!
# BMO #9, port of Rocq `Module Prefix` (BMO9.v lines 7-234, ccz181078)

Compressed steps on finite prefixes.  `E` performs `n` decrement rules and one zero rule;
`O` performs `n` decrement rules and one `(1, 1+a, …)` rule.  The index counts `E` steps.
-/

namespace BMO9.Prefix

/-- Sum of a prefix. -/
def mass (xs : List ℕ) : ℕ := xs.sum

inductive Step : ℕ → List ℕ → List ℕ → Prop
  | E (n v w : ℕ) (r : List ℕ) : Step 1 (2*n :: v :: w :: r) ((2*n+v+w+3) :: r)
  | O (n v w : ℕ) (r : List ℕ) : 1 ≤ n + v →
      Step 0 ((2*n+1) :: v :: w :: r) ((n+v-1) :: 0 :: 1 :: (w+n+1) :: r)

inductive Run : ℕ → List ℕ → List ℕ → Prop
  | refl (xs : List ℕ) : Run 0 xs xs
  | cons {e f : ℕ} {xs ys zs : List ℕ} : Step e xs ys → Run f ys zs → Run (e+f) xs zs

/-- Unlike `Run`, `Exec` may expose another zero from the infinite right tail. -/
inductive Exec : ℕ → List ℕ → List ℕ → Prop
  | stop (xs : List ℕ) : Exec 0 xs xs
  | take {e f : ℕ} {xs ys zs : List ℕ} : Step e xs ys → Exec f ys zs → Exec (e+f) xs zs
  | zero {e : ℕ} {xs ys : List ℕ} : Exec e (xs ++ [0]) ys → Exec e xs ys

theorem Run.one {e xs ys} (h : Step e xs ys) : Run e xs ys := by
  simpa using Run.cons h (Run.refl ys)

theorem Run.trans {e f xs ys zs} (h : Run e xs ys) (h' : Run f ys zs) : Run (e+f) xs zs := by
  induction h with
  | refl => simpa using h'
  | @cons e g xs ys ws hs _ ih =>
      have := Run.cons hs (ih h')
      rwa [← Nat.add_assoc] at this

theorem Step.app {e xs ys} (h : Step e xs ys) (r : List ℕ) : Step e (xs ++ r) (ys ++ r) := by
  cases h with
  | E n v w r' => exact Step.E n v w (r' ++ r)
  | O n v w r' hs => exact Step.O n v w (r' ++ r) hs

theorem Run.app {e xs ys} (h : Run e xs ys) (r : List ℕ) : Run e (xs ++ r) (ys ++ r) := by
  induction h with
  | refl => exact Run.refl _
  | cons hs _ ih => exact Run.cons (hs.app r) ih

theorem Step.mass_eq {e xs ys} (h : Step e xs ys) : mass ys = mass xs + 3*e := by
  cases h <;> simp [mass] <;> omega


theorem Run.mass_eq {e xs ys} (h : Run e xs ys) : mass ys = mass xs + 3*e := by
  induction h with
  | refl => simp
  | cons hs _ ih => rw [ih, hs.mass_eq]; ring

theorem Step.length_le {e xs ys} (h : Step e xs ys) : xs.length ≤ ys.length + 2*e := by
  cases h <;> simp

theorem Run.length_le {e xs ys} (h : Run e xs ys) : xs.length ≤ ys.length + 2*e := by
  induction h with
  | refl => simp
  | cons hs _ ih => have := hs.length_le; omega

theorem Run.exec {e xs ys} (h : Run e xs ys) : Exec e xs ys := by
  induction h with
  | refl => exact Exec.stop _
  | cons hs _ ih => exact Exec.take hs ih

theorem Exec.trans {e f xs ys zs} (h : Exec e xs ys) (h' : Exec f ys zs) :
    Exec (e+f) xs zs := by
  induction h with
  | stop => simpa using h'
  | take hs _ ih =>
      have := Exec.take hs (ih h')
      rwa [← Nat.add_assoc] at this
  | zero _ ih => exact Exec.zero (ih h')

theorem mass_zero (xs : List ℕ) : mass (xs ++ [0]) = mass xs := by simp [mass]

theorem Exec.mass_eq {e xs ys} (h : Exec e xs ys) : mass ys = mass xs + 3*e := by
  induction h with
  | stop => simp
  | take hs _ ih => rw [ih, hs.mass_eq]; ring
  | zero _ ih => rwa [mass_zero] at ih

/-- `q, 2q, 4q, …` (`k` terms). -/
def geometric : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k+1, q => q :: geometric k (2*q)

def F (k q : ℕ) : List ℕ := (q+1) :: geometric k q

def G : ℕ → ℕ → List ℕ
  | 0, q => [q]
  | k+1, q => F k q ++ [2^k*q - 1]

theorem geometric_snoc (k q : ℕ) : geometric (k+1) q = geometric k q ++ [2^k*q] := by
  induction k generalizing q with
  | zero => simp [geometric]
  | succ k ih =>
      rw [geometric, ih, geometric]
      simp [pow_succ]; ring

theorem geometric_length (k q : ℕ) : (geometric k q).length = k := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih => simp [geometric, ih]

theorem geometric_mass (k q : ℕ) : mass (geometric k q) + q = 2^k*q := by
  induction k generalizing q with
  | zero => simp [geometric, mass]
  | succ k ih =>
      have := ih (2*q)
      simp only [mass, geometric, List.sum_cons] at this ⊢
      rw [pow_succ]; linarith

theorem F_snoc (k q : ℕ) : F (k+1) q = F k q ++ [2^k*q] := by
  simp [F, geometric_snoc]

theorem odd_descent (k t w : ℕ) (r : List ℕ) :
    Run 1 ((2^k*(3+2*t) - 3) :: 0 :: 1 :: w :: r)
      ((4+2*t) :: (geometric k (3+2*t) ++ w :: r)) := by
  induction k generalizing w r with
  | zero =>
      have h := Run.one (Step.E t 0 1 (w :: r))
      simpa [geometric, show 2*t+1+3 = 4+2*t by omega] using h
  | succ k ih =>
      have hp : 3 ≤ 2^k*(3+2*t) := by
        have := Nat.one_le_two_pow (n := k); nlinarith
      have h1 := Step.O (2^k*(3+2*t) - 2) 0 1 (w :: r) (by omega)
      have h2 := ih (2^k*(3+2*t)) (w :: r)
      have h := Run.cons h1 (by convert h2 using 2 <;> simp <;> omega)
      convert h using 2
      · rw [pow_succ, mul_comm (2^k) 2, mul_assoc]; omega
      · simp [geometric_snoc]

theorem odd_expand (k t n v w : ℕ) (r : List ℕ) (h : n + v + 2 = 2^k*(3+2*t)) :
    Run 1 ((2*n+1) :: v :: w :: r) ((4+2*t) :: (geometric k (3+2*t) ++ (w+n+1) :: r)) := by
  have hp : 3 ≤ 2^k*(3+2*t) := by
    have := Nat.one_le_two_pow (n := k); nlinarith
  have h1 := Step.O n v w r (by omega)
  have h2 := odd_descent k t (w+n+1) r
  have := Run.cons h1 (by rw [show n + v - 1 = 2^k*(3+2*t) - 3 by omega]; exact h2)
  simpa using this

theorem split2 (n : ℕ) (hn : 0 < n) : ∃ k t, n = 2^k*(1+2*t) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  obtain ⟨t, rfl⟩ := hm
  exact ⟨k, t, by ring⟩

theorem not_three_dvd_two_pow (m : ℕ) : ¬ 3 ∣ 2^m := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

/-- Every singleton `[3j]` safely returns to a singleton, given the `G` returns. -/
theorem single_returns
    (HG : ∀ k t, ∃ e m, Exec e (G (k+1) (1+2*t)) [m]) :
    ∀ j, ∃ e m, Exec (1+e) [3*j] [m] := by
  intro j
  rcases Nat.even_or_odd (3*j) with ⟨n, hn⟩ | ⟨n, hn⟩
  · refine ⟨0, 2*n+3, ?_⟩
    refine Exec.zero (Exec.zero ?_)
    have := (Run.one (Step.E n 0 0 [])).exec
    simpa [hn, two_mul] using this
  · obtain ⟨k, t, hk⟩ := split2 (n+2) (by omega)
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · exfalso
        apply not_three_dvd_two_pow (k+1)
        refine ⟨j+1, ?_⟩
        rw [pow_succ]; simp at hk; omega
      · exact h
    obtain ⟨e, m, hr⟩ := HG k t
    refine ⟨e, m, Exec.zero (Exec.zero ?_)⟩
    have ho := odd_expand k (t-1) n 0 0 [] (by rw [show 3 + 2*(t-1) = 1+2*t by omega]; omega)
    rw [show 3 + 2*(t-1) = 1+2*t by omega, show 4 + 2*(t-1) = (1+2*t)+1 by omega] at ho
    have hG : G (k+1) (1+2*t) = (1+2*t+1) :: (geometric k (1+2*t) ++ [0+n+1]) := by
      simp [G, F]; omega
    rw [hG] at hr
    simpa [hn] using ho.exec.trans hr

theorem snoc_inj {p p' : List ℕ} {z z' : ℕ} (h : p ++ [z] = p' ++ [z']) : p = p' ∧ z = z' := by
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

theorem Step.last {e xs ys} (h : Step e xs ys) (p : List ℕ) (z : ℕ) (hx : xs = p ++ [z]) :
    ∃ q d, ys = q ++ [z+d] ∧ ∀ z', Step e (p ++ [z']) (q ++ [z'+d]) := by
  cases h with
  | E n v w r =>
      rcases List.eq_nil_or_concat r with rfl | ⟨p0, z0, rfl⟩
      · obtain ⟨rfl, rfl⟩ := snoc_inj (p := [2*n, v]) (by simpa using hx)
        refine ⟨[], 2*n+v+3, by simp; omega, fun z' ↦ ?_⟩
        rw [show z' + (2*n+v+3) = 2*n+v+z'+3 by omega]
        exact Step.E n v z' []
      · obtain ⟨rfl, rfl⟩ := snoc_inj (p := 2*n :: v :: w :: p0) (by simpa using hx)
        exact ⟨(2*n+v+w+3) :: p0, 0, by simp, fun z' ↦ by simpa using Step.E n v w (p0 ++ [z'])⟩
  | O n v w r hs =>
      rcases List.eq_nil_or_concat r with rfl | ⟨p0, z0, rfl⟩
      · obtain ⟨rfl, rfl⟩ := snoc_inj (p := [2*n+1, v]) (by simpa using hx)
        refine ⟨[n+v-1, 0, 1], n+1, by simp; omega, fun z' ↦ ?_⟩
        rw [show z' + (n+1) = z'+n+1 by omega]
        exact Step.O n v z' [] hs
      · obtain ⟨rfl, rfl⟩ := snoc_inj (p := (2*n+1) :: v :: w :: p0) (by simpa using hx)
        exact ⟨(n+v-1) :: 0 :: 1 :: (w+n+1) :: p0, 0, by simp,
          fun z' ↦ by simpa using Step.O n v w (p0 ++ [z']) hs⟩

theorem Run.last {e xs ys} (h : Run e xs ys) :
    ∀ (p : List ℕ) (z : ℕ), xs = p ++ [z] →
      ∃ q d, ys = q ++ [z+d] ∧ ∀ z', Run e (p ++ [z']) (q ++ [z'+d]) := by
  induction h with
  | refl xs => intro p z hx; exact ⟨p, 0, by simpa using hx, fun z' ↦ by simpa using Run.refl _⟩
  | cons hs _ ih =>
      intro p z hx
      obtain ⟨p1, d1, hy, hstep⟩ := hs.last p z hx
      obtain ⟨p2, d2, hz, hrun⟩ := ih p1 (z+d1) hy
      refine ⟨p2, d1+d2, by rw [hz, Nat.add_assoc], fun z' ↦ ?_⟩
      have := Run.cons (hstep z') (hrun (z'+d1))
      rwa [Nat.add_assoc] at this

theorem F_to_G (e k q : ℕ) (ys : List ℕ) (a : ℕ) (hq : 0 < q)
    (h : Run e (F (k+1) q) (ys ++ [1+a])) : Run e (G (k+1) q) (ys ++ [a]) := by
  obtain ⟨p, d, he, hr⟩ := h.last _ _ (F_snoc k q)
  obtain ⟨rfl, ha⟩ := snoc_inj he
  have hp : 0 < 2^k := Nat.two_pow_pos k
  have := hr (2^k*q - 1)
  have hq' : 1 ≤ 2^k*q := Nat.one_le_iff_ne_zero.2 (by positivity)
  rw [show 2^k*q - 1 + d = a by omega] at this
  simpa [G] using this

theorem odd_lookup (k t n v w : ℕ) (r : List ℕ) (e : ℕ) (ys : List ℕ) (a : ℕ)
    (hn : n + v + 2 = 2^k*(3+2*t)) (hr : Run e (F (k+1) (3+2*t)) (ys ++ [a])) :
    Run (1+e) ((2*n+1) :: v :: w :: r) ((ys ++ [a+w-v-1]) ++ r) := by
  obtain ⟨p, d, hlast, hrun⟩ := hr.last _ _ (F_snoc k (3+2*t))
  obtain ⟨rfl, ha⟩ := snoc_inj hlast
  have h1 := odd_expand k t n v w r hn
  have h2 := (hrun (w+n+1)).app r
  have h1' : Run 1 ((2*n+1) :: v :: w :: r) ((F k (3+2*t) ++ [w+n+1]) ++ r) := by
    simpa [F, show 3+2*t+1 = 4+2*t by omega] using h1
  have := h1'.trans h2
  convert this using 3
  simp; omega
