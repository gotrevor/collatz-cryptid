import Mathlib

/-!
# Beaver Math Olympiad problem 3 — no term is a power of four

BMO#3 is the mathematical reformulation of the non-halting of the 2-state 5-symbol Turing
machine `1RB0RB3LA4LA2RA_2LB3RA---3RA4RB` from the all-0 tape.

Starting from `a 0 = 2`, each step adds `2 ^ (v₂ (a n) + 2) - 1`, where `v₂` is the 2-adic
valuation.  The question is whether any term is a power of four.  None is.

## The mechanism

Terms alternate parity: an even term gains an odd amount, an odd term gains exactly `3`.
So powers of four — even, for a positive exponent — can only occur at even indices, and it
suffices to study `T m = a (2 * m) / 2`, which satisfies the one-step recurrence
`T (m + 1) = T m + 2 ^ (v₂ (T m) + 2) + 1`.

That halved sequence is *self-similar*:

* `T (2 * m) + 1 = 2 * T m + 4 * m`
* `T (2 * m + 1) = 2 * T m + 4 * m + 4`

and those two identities force the **ruler lemma** `v₂ (T m) = v₂ (m + 1)` — the valuations
of `T` reproduce the ruler sequence `1, 2, 1, 3, 1, 2, 1, 4, …`.  All three facts are proved
by a single strong induction, since each feeds the others.

The ruler lemma is what makes the problem finite.  If `a (2 * m) = 4 ^ k` then `T m` is
`2 ^ (2 * k - 1)`, so `v₂ (m + 1) = 2 * k - 1` and hence `m + 1 ≥ 2 ^ (2 * k - 1)`.  But the
sequence also grows by at least `10` per even step, so `a (2 * m) ≥ 10 * m + 2`, which already
exceeds `4 ^ k` by a factor of nearly five.  The two bounds cannot both hold.

*References:*

- [Beaver Math Olympiad wiki page](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) (§3);
  the machine was found and informally proved non-halting by bbchallenge contributor
  Daniel Yuan, June 2024.  The wiki's §3 *Formalised solution* line links an initial
  announcement, a Lean proof and an LLM-translated Rocq proof, but all four links are
  bbchallenge Discord messages rather than a repository, and a public GitHub code search
  for `beaver_math_olympiad` and for the machine's transition string finds no formalization
  (both checked 2026-08-25).  The argument here was worked out independently rather than
  ported.
- Statement as posed in
  [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean)
-/

namespace Collatz.BMO.Problem3

/-! ## A minimal 2-adic valuation API -/

private lemma val2_odd {x : ℕ} (hx : x % 2 = 1) : padicValNat 2 x = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

private lemma val2_two_mul {x : ℕ} (hx : x ≠ 0) :
    padicValNat 2 (2 * x) = padicValNat 2 x + 1 := by
  rw [padicValNat.mul (by norm_num) hx, padicValNat.self (by norm_num)]
  omega

private lemma val2_pow_mul_odd {s z : ℕ} (hz : z % 2 = 1) :
    padicValNat 2 (2 ^ s * z) = s := by
  have hz0 : z ≠ 0 := by omega
  rw [padicValNat.mul (by positivity) hz0, padicValNat.prime_pow, val2_odd hz, add_zero]

private lemma four_le_two_pow (v : ℕ) : 4 ≤ 2 ^ (v + 2) := by
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
  _ ≤ 2 ^ (v + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma two_dvd_two_pow (v : ℕ) : 2 ∣ 2 ^ (v + 2) :=
  dvd_pow_self 2 (by omega)

/-! ## Basic facts about the sequence -/

section
variable {a : ℕ → ℕ}
  (a_ini : a 0 = 2)
  (a_rec : ∀ n, a (n + 1) = a n + 2 ^ (padicValNat 2 (a n) + 2) - 1)

include a_ini a_rec

/-- Every term is at least `2`; in particular no term is `4 ^ 0 = 1`. -/
theorem two_le (n : ℕ) : 2 ≤ a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h4 := four_le_two_pow (padicValNat 2 (a n))
    have := a_rec n
    omega

omit a_ini in
/-- An even term is followed by an odd one. -/
theorem odd_succ_of_even {n : ℕ} (h : a n % 2 = 0) : a (n + 1) % 2 = 1 := by
  have h4 := four_le_two_pow (padicValNat 2 (a n))
  have h2 := two_dvd_two_pow (padicValNat 2 (a n))
  have := a_rec n
  omega

omit a_ini in
/-- An odd term is followed by its successor-plus-three, hence by an even one. -/
theorem succ_of_odd {n : ℕ} (h : a n % 2 = 1) : a (n + 1) = a n + 3 := by
  have hv : padicValNat 2 (a n) = 0 := val2_odd h
  have := a_rec n
  rw [hv] at this
  norm_num at this
  omega

omit a_ini in
theorem even_succ_of_odd {n : ℕ} (h : a n % 2 = 1) : a (n + 1) % 2 = 0 := by
  have := succ_of_odd a_rec h
  omega

/-- The sequence strictly alternates parity, starting even. -/
theorem parity (m : ℕ) : a (2 * m) % 2 = 0 ∧ a (2 * m + 1) % 2 = 1 := by
  induction m with
  | zero =>
    have h0 : a (2 * 0) % 2 = 0 := by norm_num [a_ini]
    exact ⟨h0, odd_succ_of_even a_rec h0⟩
  | succ m ih =>
    obtain ⟨he, ho⟩ := ih
    have h1 : a (2 * m + 2) % 2 = 0 := even_succ_of_odd a_rec ho
    have h2 : a (2 * (m + 1)) % 2 = 0 := by
      have : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [this]; exact h1
    refine ⟨h2, ?_⟩
    exact odd_succ_of_even a_rec h2

end

/-! ## The halved even-indexed subsequence

Terms alternate parity, so the even-indexed ones carry all the information about powers of
four.  Halving them turns the two-step recurrence into a one-step one. -/

/-- `T a m = a (2 * m) / 2`. -/
def T (a : ℕ → ℕ) (m : ℕ) : ℕ := a (2 * m) / 2

section
variable {a : ℕ → ℕ}
  (a_ini : a 0 = 2)
  (a_rec : ∀ n, a (n + 1) = a n + 2 ^ (padicValNat 2 (a n) + 2) - 1)

include a_ini a_rec

theorem two_mul_T (m : ℕ) : a (2 * m) = 2 * T a m := by
  have := (parity a_ini a_rec m).1
  simp only [T]
  omega

theorem T_pos (m : ℕ) : 1 ≤ T a m := by
  have h2 := two_le a_ini a_rec (2 * m)
  have := two_mul_T a_ini a_rec m
  omega

/-- The one-step recurrence for the halved even-indexed subsequence. -/
theorem T_rec (m : ℕ) : T a (m + 1) = T a m + 2 ^ (padicValNat 2 (T a m) + 2) + 1 := by
  have hpos := T_pos a_ini a_rec m
  have hTm := two_mul_T a_ini a_rec m
  -- the valuation at the even index is one more than at the halved value
  have hv : padicValNat 2 (a (2 * m)) = padicValNat 2 (T a m) + 1 := by
    rw [hTm]; exact val2_two_mul (by omega)
  set t := padicValNat 2 (T a m) with ht
  have hstep1 : a (2 * m + 1) = a (2 * m) + 2 ^ (t + 3) - 1 := by
    have := a_rec (2 * m)
    rw [hv] at this
    have h3 : t + 1 + 2 = t + 3 := by omega
    rw [h3] at this
    exact this
  have hodd : a (2 * m + 1) % 2 = 1 := (parity a_ini a_rec m).2
  have hstep2 : a (2 * m + 1 + 1) = a (2 * m + 1) + 3 := succ_of_odd a_rec hodd
  have hpow : (2 : ℕ) ^ (t + 3) = 2 * 2 ^ (t + 2) := by ring
  have hbig : a (2 * (m + 1)) = 2 * (T a m + 2 ^ (t + 2) + 1) := by
    have hidx : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [hidx, hstep2, hstep1, hTm]
    have h4 : (4 : ℕ) ≤ 2 ^ (t + 3) := four_le_two_pow (t + 1)
    omega
  simp only [T, hbig]
  omega

/-- A crude but sufficient growth bound: each step adds at least `5`. -/
theorem T_ge (m : ℕ) : 5 * m + 1 ≤ T a m := by
  induction m with
  | zero =>
    have := T_pos a_ini a_rec 0
    omega
  | succ m ih =>
    have hr := T_rec a_ini a_rec m
    have h4 := four_le_two_pow (padicValNat 2 (T a m))
    omega

end

/-! ## Self-similarity and the ruler lemma

The three facts below are proved by a single strong induction because they feed each other:
the doubling identities at `m + 1` need the odd-part decomposition at `m`, while the odd-part
decomposition at `m` needs the doubling identities at `m / 2`. -/

section
variable {a : ℕ → ℕ}
  (a_ini : a 0 = 2)
  (a_rec : ∀ n, a (n + 1) = a n + 2 ^ (padicValNat 2 (a n) + 2) - 1)

include a_ini a_rec

theorem selfSimilar (m : ℕ) :
    (T a (2 * m) + 1 = 2 * T a m + 4 * m) ∧
    (T a (2 * m + 1) = 2 * T a m + 4 * m + 4) ∧
    (∃ t z w, z % 2 = 1 ∧ w % 2 = 1 ∧ T a m = 2 ^ t * z ∧ m + 1 = 2 ^ t * w) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hT0 : T a 0 = 1 := by simp only [T]; norm_num [a_ini]
  -- Step 1: the odd-part decomposition at `m`, from the doubling identities at `m / 2`.
  have ruler : ∃ t z w, z % 2 = 1 ∧ w % 2 = 1 ∧ T a m = 2 ^ t * z ∧ m + 1 = 2 ^ t * w := by
    rcases Nat.even_or_odd m with he | ho
    · -- `m = 2 * j`; then `T a m` is odd and so is `m + 1`.
      obtain ⟨j, hj⟩ := he
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact ⟨0, 1, 1, by norm_num, by norm_num, by simpa [hj] using hT0, by simp [hj]⟩
      · have hjm : j < m := by omega
        have hA := (ih j hjm).1
        have hpos := T_pos a_ini a_rec j
        have hodd : T a m % 2 = 1 := by
          have : T a (2 * j) + 1 = 2 * T a j + 4 * j := hA
          have hmj : m = 2 * j := by omega
          rw [hmj]; omega
        exact ⟨0, T a m, m + 1, hodd, by omega, by norm_num, by norm_num⟩
    · -- `m = 2 * j + 1`; the decomposition at `j` doubles.
      obtain ⟨j, hj⟩ := ho
      have hjm : j < m := by omega
      obtain ⟨hAj, hBj, t, z, w, hz, hw, hTj, hj1⟩ := ih j hjm
      refine ⟨t + 1, z + 2 * w, w, by omega, hw, ?_, ?_⟩
      · have hpow : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
        have hTm : T a m = 2 * T a j + 4 * j + 4 := by rw [hj]; exact hBj
        rw [hTm, hTj, hpow]
        have hring : 2 * (2 ^ t * z) + 4 * (2 ^ t * w) = 2 * 2 ^ t * (z + 2 * w) := by ring
        omega
      · have hpow : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
        have : m + 1 = 2 * (j + 1) := by omega
        rw [this, hj1, hpow]
        ring
  -- Step 2: the doubling identities at `m`, from those at `m - 1` plus its decomposition.
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · refine ⟨by simp [hT0], ?_, ruler⟩
    have h1 := T_rec a_ini a_rec 0
    rw [hT0] at h1
    norm_num [val2_odd] at h1
    simpa [hT0] using h1
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨hA', hB', t, z, w, hz, hw, hTm', hm1'⟩ := ih m' (by omega)
    -- valuations of the two relevant terms, read off their odd parts
    have hvm' : padicValNat 2 (T a m') = t := by rw [hTm']; exact val2_pow_mul_odd hz
    have hodd1 : T a (2 * m' + 1) = 2 ^ (t + 1) * (z + 2 * w) := by
      have hpow : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
      rw [hB', hTm', hpow]
      have hring : 2 * (2 ^ t * z) + 4 * (2 ^ t * w) = 2 * 2 ^ t * (z + 2 * w) := by ring
      omega
    have hv1 : padicValNat 2 (T a (2 * m' + 1)) = t + 1 := by
      rw [hodd1]; exact val2_pow_mul_odd (by omega)
    -- unfold the recurrence twice, at `2m'+1` and at `2m'+2`
    have hrec1 := T_rec a_ini a_rec (2 * m' + 1)
    rw [hv1] at hrec1
    have hidx1 : 2 * m' + 1 + 1 = 2 * (m' + 1) := by ring
    rw [hidx1] at hrec1
    have hrecm' := T_rec a_ini a_rec m'
    rw [hvm'] at hrecm'
    have hp3 : (2 : ℕ) ^ (t + 1 + 2) = 2 * 2 ^ (t + 2) := by ring
    have hA : T a (2 * (m' + 1)) + 1 = 2 * T a (m' + 1) + 4 * (m' + 1) := by
      rw [hrec1, hB', hrecm', hp3]; ring
    refine ⟨hA, ?_, ruler⟩
    -- `T a (2 * (m' + 1))` is odd, so the next step adds exactly `5`
    have hpos := T_pos a_ini a_rec (m' + 1)
    have hoddA : T a (2 * (m' + 1)) % 2 = 1 := by omega
    have hv2 : padicValNat 2 (T a (2 * (m' + 1))) = 0 := val2_odd hoddA
    have hrec2 := T_rec a_ini a_rec (2 * (m' + 1))
    rw [hv2] at hrec2
    norm_num at hrec2
    omega

end

/-! ## The headline

Statement transcribed verbatim from `google-deepmind/formal-conjectures`,
`FormalConjectures/Other/BeaverMathOlympiad.lean`. -/

/-- **BMO#3.** No term of the sequence is a power of four.

If `a n = 4 ^ k` then `n` is even (odd-indexed terms are odd) and `k ≥ 1` (every term is at
least `2`).  Writing `n = 2 * m`, the ruler lemma forces the `2`-adic valuation of `m + 1` to
be `2 * k - 1`, so `m + 1 ≥ 2 ^ (2 * k - 1)`.  But the sequence grows by at least `10` per
even step, so `a (2 * m) ≥ 10 * m + 2 ≥ 5 * 4 ^ k - 8 > 4 ^ k`. -/
theorem beaver_math_olympiad_problem_3
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) = (a n) + 2 ^ ((padicValNat 2 (a n)) + 2) - 1) :
    ¬ (∃ n k, a n = 4 ^ k) := by
  rintro ⟨n, k, hnk⟩
  have h2 := two_le a_ini a_rec n
  -- `k = 0` would make `a n = 1`, but every term is at least `2`.
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · norm_num at hnk; omega
    · exact ⟨k - 1, by omega⟩
  -- `4 ^ (k' + 1)` is even, so `n` cannot be an odd index.
  have hfour : (4 : ℕ) ^ (k' + 1) = 2 * 2 ^ (2 * k' + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
    ring
  have heven : a n % 2 = 0 := by rw [hnk, hfour]; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨j, hj⟩ := he; exact ⟨j, by omega⟩
    · obtain ⟨j, hj⟩ := ho
      rw [hj] at heven
      have := (parity a_ini a_rec j).2
      omega
  -- Halve: `T a m = 2 ^ (2 * k' + 1)`.
  have hTm : T a m = 2 ^ (2 * k' + 1) := by
    have h := two_mul_T a_ini a_rec m
    rw [hnk, hfour] at h
    omega
  -- The ruler lemma pins the valuation of `m + 1`.
  obtain ⟨-, -, t, z, w, hz, hw, hTz, hmw⟩ := selfSimilar a_ini a_rec m
  have hzdvd : z ∣ 2 ^ (2 * k' + 1) := ⟨2 ^ t, by rw [← hTm, hTz]; ring⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hzdvd
  have hi : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · exfalso
      have : (2 : ℕ) ∣ 2 ^ i := dvd_pow_self 2 (by omega)
      omega
  subst hi
  have ht : t = 2 * k' + 1 := by
    have : (2 : ℕ) ^ t = 2 ^ (2 * k' + 1) := by
      rw [← hTm, hTz]; ring
    exact Nat.pow_right_injective (le_refl 2) this
  subst ht
  -- `m + 1` is a positive multiple of `2 ^ (2 * k' + 1)`, hence at least that big.
  have hw1 : 1 ≤ w := by omega
  have hlow : 2 ^ (2 * k' + 1) ≤ m + 1 := by
    have := Nat.mul_le_mul_left (2 ^ (2 * k' + 1)) hw1
    rw [mul_one] at this
    omega
  -- but the growth bound caps it
  have hgrow := T_ge a_ini a_rec m
  have hX : 2 ≤ 2 ^ (2 * k' + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 * k' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## Sanity anchors

The recurrence above is transcribed from the BMO wiki, which prints the opening terms
`2, 9, 12, 27, 30, 37, 40, 71, 74, 81`.  Checking a prefix guards the transcription. -/

private lemma val2_twelve : padicValNat 2 12 = 2 := by
  have h := val2_pow_mul_odd (s := 2) (z := 3) (by norm_num)
  norm_num at h
  exact h

private lemma val2_thirty : padicValNat 2 30 = 1 := by
  have h := val2_pow_mul_odd (s := 1) (z := 15) (by norm_num)
  norm_num at h
  exact h

example (a : ℕ → ℕ) (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) = a n + 2 ^ (padicValNat 2 (a n) + 2) - 1) :
    a 1 = 9 ∧ a 2 = 12 ∧ a 3 = 27 ∧ a 4 = 30 ∧ a 5 = 37 := by
  have h0 := a_rec 0
  rw [a_ini, padicValNat.self (by norm_num)] at h0
  norm_num at h0
  have h1 := a_rec 1
  rw [h0, val2_odd (by norm_num)] at h1
  norm_num at h1
  have h2 := a_rec 2
  rw [h1, val2_twelve] at h2
  norm_num at h2
  have h3 := a_rec 3
  rw [h2, val2_odd (by norm_num)] at h3
  norm_num at h3
  have h4 := a_rec 4
  rw [h3, val2_thirty] at h4
  norm_num at h4
  exact ⟨h0, h1, h2, h3, h4⟩

-- Axiom audit.
#print axioms Collatz.BMO.Problem3.selfSimilar
#print axioms Collatz.BMO.Problem3.beaver_math_olympiad_problem_3

end Collatz.BMO.Problem3
