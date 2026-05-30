import Mathlib

/-!
# The Lagarias cycle remainder and its rotation symmetry

A `3x+d` cycle with `n` odd-steps and halving-vector `e = (e₁,…,eₙ)` (each
`eᵢ ≥ 1`, `L = Σ eᵢ`) satisfies the Lagarias cycle equation

  `x · (2^L − 3^n) = d · R(e)`,   `R(e) = Σ_{j=1}^n 3^{n−j} · 2^{S_{j-1}}`,

`S_{j-1} = e₁+…+e_{j-1}`.  So `gap := 2^L − 3^n` — **"2 ≠ 3" made into a
number** — divides `d·R(e)`, and the `d=1` (Collatz) cycle candidates are
exactly the `e` with `gap ∣ R(e)`.

A cycle is a *set*; which element you call `x` is a free choice of starting
point.  Cyclically rotating `e` re-bases the cycle at the next element.  This
file proves that this rotation acts cleanly on `R` modulo `gap` — making
"a cycle doesn't care where you start" a theorem read off `R mod gap`.

## Results
* `cycleR_rotate` — the exact (subtraction-free) identity
  `2^{e₁}·R(e') + 3^n = 3·R(e) + 2^L`  where `e' = rotate(e)`.
* `cycleR_rotate_int` — its ℤ form `2^{e₁}·R(e') = 3·R(e) + gap`.
* `cycleGap_dvd_cycleR_iff` — `gap ∣ R(e) ⟺ gap ∣ R(e')`
  (rotation-invariance of the cycle divisibility; uses `gap` odd ∧ `3 ∤ gap`).

Empirical companion: `notes/24-re-mod-gap-rotation.md` (the probe that found
the rotation orbits, and rediscovered the negative cycles `x = −5, −17`).
-/

namespace Collatz.Erdos

/-- The **Lagarias cycle remainder** of an exponent vector `e`, in the
recursive form `R(a :: rest) = 3^{|rest|} + 2^a · R(rest)`, `R([]) = 0`.
Equivalently `R(e) = Σ_{j=1}^n 3^{n-j} 2^{S_{j-1}}`. -/
def cycleR : List ℕ → ℕ
  | [] => 0
  | a :: rest => 3 ^ rest.length + 2 ^ a * cycleR rest

@[simp] theorem cycleR_nil : cycleR [] = 0 := rfl

theorem cycleR_cons (a : ℕ) (l : List ℕ) :
    cycleR (a :: l) = 3 ^ l.length + 2 ^ a * cycleR l := rfl

/-- Appending a final exponent: `R(l ++ [a]) = 3·R(l) + 2^{Σl}`.
(The appended value `a` does not appear — it sits at the last position, whose
coefficient `3^0·2^{Σl}` ignores it.) -/
theorem cycleR_append_single (a : ℕ) (l : List ℕ) :
    cycleR (l ++ [a]) = 3 * cycleR l + 2 ^ l.sum := by
  induction l with
  | nil => simp [cycleR]
  | cons b t ih =>
    have hlen : (t ++ [a]).length = t.length + 1 := by simp
    rw [List.cons_append, cycleR_cons, hlen, ih, cycleR_cons, List.sum_cons,
        pow_succ, pow_add]
    ring

/-- The **"2 ≠ 3" gap** of an exponent vector: `2^L − 3^n` in ℤ. -/
def cycleGap (e : List ℕ) : ℤ := 2 ^ e.sum - 3 ^ e.length

/-- **Rotation identity (ℕ, exact, subtraction-free).** For `e = a :: rest` with
one-step rotation `e' = rest ++ [a]`:
`2^a · R(e') + 3^n = 3 · R(e) + 2^L`. -/
theorem cycleR_rotate (a : ℕ) (rest : List ℕ) :
    2 ^ a * cycleR (rest ++ [a]) + 3 ^ (a :: rest).length
      = 3 * cycleR (a :: rest) + 2 ^ (a :: rest).sum := by
  rw [cycleR_append_single, cycleR_cons, List.length_cons, List.sum_cons,
      pow_succ, pow_add]
  ring

/-- **Rotation identity (ℤ).** `2^a · R(e') = 3 · R(e) + gap`. -/
theorem cycleR_rotate_int (a : ℕ) (rest : List ℕ) :
    (2 : ℤ) ^ a * (cycleR (rest ++ [a]) : ℤ)
      = 3 * (cycleR (a :: rest) : ℤ) + cycleGap (a :: rest) := by
  have h := cycleR_rotate a rest
  have hz : ((2 ^ a * cycleR (rest ++ [a]) + 3 ^ (a :: rest).length : ℕ) : ℤ)
          = ((3 * cycleR (a :: rest) + 2 ^ (a :: rest).sum : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at hz
  unfold cycleGap
  linarith

/-- `gap` is odd whenever `L = Σe ≥ 1` (always true for a genuine composition
into positive parts): `2^L` is even, `3^n` is odd. -/
theorem cycleGap_odd (a : ℕ) (rest : List ℕ) (hL : 1 ≤ (a :: rest).sum) :
    Odd (cycleGap (a :: rest)) := by
  unfold cycleGap
  have heven : Even ((2 : ℤ) ^ (a :: rest).sum) := by
    obtain ⟨t, ht⟩ : ∃ t, (a :: rest).sum = t + 1 := ⟨(a :: rest).sum - 1, by omega⟩
    rw [ht, pow_succ]
    exact even_two.mul_left _
  exact heven.sub_odd ((by norm_num : Odd (3 : ℤ)).pow)

/-- `3 ∤ gap`: mod 3, `gap ≡ 2^L ≡ (±1) ≠ 0` (and `3 ∣ 3^n` since `n ≥ 1`). -/
theorem not_three_dvd_cycleGap (a : ℕ) (rest : List ℕ) :
    ¬ (3 : ℤ) ∣ cycleGap (a :: rest) := by
  unfold cycleGap
  intro hdvd
  have hn : (a :: rest).length ≠ 0 := by simp
  have h3n : (3 : ℤ) ∣ 3 ^ (a :: rest).length := dvd_pow_self 3 hn
  have h2s : (3 : ℤ) ∣ 2 ^ (a :: rest).sum := by
    have hd := dvd_add hdvd h3n
    have hcancel : (2 : ℤ) ^ (a :: rest).sum - 3 ^ (a :: rest).length
                     + 3 ^ (a :: rest).length = 2 ^ (a :: rest).sum := by ring
    rwa [hcancel] at hd
  have h32 : (3 : ℤ) ∣ 2 := (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h2s
  norm_num at h32

/-- **Rotation-invariance of the cycle divisibility** (the keeper).
`gap ∣ R(e) ⟺ gap ∣ R(e')` for the one-step rotation `e' = rest ++ [a]`.
So the `d=1` Collatz cycle candidates come in full ℤ/n rotation orbits. -/
theorem cycleGap_dvd_cycleR_iff (a : ℕ) (rest : List ℕ) (hL : 1 ≤ (a :: rest).sum) :
    cycleGap (a :: rest) ∣ (cycleR (a :: rest) : ℤ)
      ↔ cycleGap (a :: rest) ∣ (cycleR (rest ++ [a]) : ℤ) := by
  have hid : (2 : ℤ) ^ a * (cycleR (rest ++ [a]) : ℤ)
           = 3 * (cycleR (a :: rest) : ℤ) + cycleGap (a :: rest) := cycleR_rotate_int a rest
  have hcop2 : IsCoprime (cycleGap (a :: rest)) ((2 : ℤ) ^ a) := by
    have hnd : ¬ (2 : ℤ) ∣ cycleGap (a :: rest) := by
      have hodd := Int.odd_iff.mp (cycleGap_odd a rest hL)
      intro hd
      obtain ⟨k, hk⟩ := hd
      omega
    exact (((by norm_num : Prime (2 : ℤ)).coprime_iff_not_dvd).mpr hnd).symm.pow_right
  have hcop3 : IsCoprime (cycleGap (a :: rest)) (3 : ℤ) :=
    (((by norm_num : Prime (3 : ℤ)).coprime_iff_not_dvd).mpr
      (not_three_dvd_cycleGap a rest)).symm
  constructor
  · intro h
    have h1 : cycleGap (a :: rest) ∣ 3 * (cycleR (a :: rest) : ℤ) + cycleGap (a :: rest) :=
      dvd_add (h.mul_left 3) (dvd_refl _)
    rw [← hid] at h1
    exact hcop2.dvd_of_dvd_mul_left h1
  · intro h
    have h1 : cycleGap (a :: rest) ∣ (2 : ℤ) ^ a * (cycleR (rest ++ [a]) : ℤ) := h.mul_left _
    rw [hid] at h1
    have h2 : cycleGap (a :: rest) ∣ 3 * (cycleR (a :: rest) : ℤ) := by
      have hsub := dvd_sub h1 (dvd_refl (cycleGap (a :: rest)))
      simpa using hsub
    exact hcop3.dvd_of_dvd_mul_left h2

/-- **Corollary (fork 2 → fork 1).** For the `3x+d` cycle through `x = 1`
(equation `d · R(e) = gap`), the modulus `d` is coprime to 3.  This explains the
empirical fact (`re_one_cycle_d.py`) that the "1-cycle d's" all lie in `d ≡ ±1
(mod 6)`: it is forced by `3 ∤ gap`. -/
theorem three_not_dvd_one_cycle_d {d : ℤ} {a : ℕ} {rest : List ℕ}
    (h : d * (cycleR (a :: rest) : ℤ) = cycleGap (a :: rest)) : ¬ (3 : ℤ) ∣ d := by
  intro h3
  exact not_three_dvd_cycleGap a rest (h ▸ h3.mul_right _)

/-! ## Sanity checks against `notes/24` (the negative Collatz cycles) -/

/-- `x = −5` cycle: primitive `e = (1,2)` at `n=2, L=3`, `gap = −1`, `R = 3 + 2 = 5`. -/
example : cycleR [1, 2] = 5 := by decide
example : cycleGap [1, 2] = -1 := by decide

/-- `x = −17` cycle: `e = (1,1,1,2,1,1,4)` at `n=7, L=11`, `gap = −139`,
`R = 2363 = 17 · 139`. -/
example : cycleR [1, 1, 1, 2, 1, 1, 4] = 2363 := by decide
example : cycleGap [1, 1, 1, 2, 1, 1, 4] = -139 := by decide
example : ((-139 : ℤ)) ∣ (cycleR [1, 1, 1, 2, 1, 1, 4] : ℤ) := by decide

/-- `3x+11` cycle through `1`: `e = (1,5)`, `R = 5`, `gap = 55 = 11·5`; and `3 ∤ 11`. -/
example : cycleR [1, 5] = 5 := by decide
example : cycleGap [1, 5] = 55 := by decide
example : ¬ (3 : ℤ) ∣ 11 :=
  three_not_dvd_one_cycle_d (a := 1) (rest := [5]) (by decide)

end Collatz.Erdos
