/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic
import Collatz.Bigfoot.Clock

/-!
# A census of shared engines among the cryptids

All maps are written in int-y1's `Hydra` schema (`Collatz.Bigfoot.Hydra`, transcribed from
`int-y1/proofs/BBfLean/Cryptid.lean`): `x ↦ p⌊x/q⌋ + g[x mod q]`, walk `y ↦ y + w[x mod q]`,
and the cryptid is the claim `y ≥ 0` forever.

The two canonical floor engines are
* `H(u) = ⌊3u/2⌋ = 3⌊u/2⌋ + (u mod 2)`, i.e. `hydraIterate 3 2 [0, 1]`;
* `K(u) = ⌊4u/3⌋ = 4⌊u/3⌋ + (u mod 3)`, i.e. `hydraIterate 4 3 [0, 1, 2]`.

Results (each a theorem below):
* **Antihydra is `A 3`**, where `A m` is `H` from `2^m`, counter `0`, walk `+2` (even) / `−1`
  (odd).  (Definitional, from sligocki's validator rules 4–6, start `A(8, 0)`.)
* **int-y1 #323 is `A 1`** (`hydra323_iff_A1`): `x + 2` follows `H`, with Antihydra's walk.
* **BB(2,5) Hydra is `H` from `3` with the mirrored walk** (`hydraBB25_iff`): `a = 3u − 6`.
  (Prior work: the substitution `B(a, b) = (3a − 6, b)` appears in dyuan01's analysis on the
  bbchallenge wiki page of `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`, found by web search,
  page not opened.)
* **#323 and BB(2,5) Hydra share one orbit** (`hydra323_hydraBB25_same_orbit`): both walk the
  parity sequence of `H^k(3)`, with mirrored weights (`+2/−1` from counter `2`, against `−1/+2` from
  counter `0`).
* `A 0` and `A 4` halt (`not_A0`, `not_A4`, at walk steps 1 and 22).
* **#218's engine is `K`** (`hydra218_iff`): `x + 3` follows `⌊4u/3⌋`.
* Bigfoot is `Hydra 32 24 …` (`Collatz.Bigfoot.Dyn.nonhalt_iff_hydra`), slope `4/3` like #218,
  but its block map is **not** affinely conjugate to any 4-fold floor/ceil composition of `K`
  (computed only; see `notes/32`).
-/

namespace Collatz.Census

open Collatz.Bigfoot

/-- Antihydra (BB(6) `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) in the `Hydra` schema.  Source:
sligocki `rust/src/validator.rs`, `test_antihydra`, rules 4–6: `A(2a, b) → A(3a, b+2)`,
`A(2a+1, b+1) → A(3a+1, b)`, `A(2a+1, 0) → Halt`, start `A(8, 0)`. -/
def antihydra : Prop := Hydra 3 2 [0, 1] [2, -1] (8, 0)

/-- `A m`: Antihydra's engine `H` and walk, started at `2^m` with counter `0`. -/
def A (m : ℕ) : Prop := Hydra 3 2 [0, 1] [2, -1] ((2 : ℤ) ^ m, 0)

/-- int-y1's BBf #323 (`Size23Summary.lean`, `hydra323`). -/
def hydra323 : Prop := Hydra 3 2 [1, 2] [2, -1] (1, 2)

/-- BB(2,5) Hydra (`1RB3RB---3LA1RA_2LA3RA4LB0LB0LA`) in the `Hydra` schema.  Source: sligocki
`rust/src/validator.rs`, `test_hydra`: `A(2n, 0) → Halt`, `A(2n, b+1) → A(3n+3, b)`,
`A(2n+1, b) → A(3n+3, b+2)`, start `A(3, 0)`. -/
def hydraBB25 : Prop := Hydra 3 2 [3, 3] [-1, 2] (3, 0)

/-- int-y1's BBf #218 (`Size23Summary.lean`, `hydra218`). -/
def hydra218 : Prop := Hydra 4 3 [1, 2, 3] [3, 1, -1] (1, 3)

theorem antihydra_iff_A3 : antihydra ↔ A 3 := by
  unfold antihydra A; norm_num

/-! ## Transfer along a semiconjugacy -/

/-- If `φ` semiconjugates `g` to `f` and preserves the walk coordinate, the `Hydra` predicates
agree. -/
theorem hydra_transfer {f g : ℤ × ℤ → ℤ × ℤ} (φ : ℤ × ℤ → ℤ × ℤ)
    (h : ∀ p, φ (g p) = f (φ p)) (h2 : ∀ p, (φ p).2 = p.2) (p : ℤ × ℤ) (n : ℕ) :
    (f^[n] (φ p)).2 = (g^[n] p).2 := by
  have hs : Function.Semiconj φ g f := h
  rw [← hs.iterate_right n p, h2]

/-- One step of `H` with walk `w`. -/
theorem hydraIterate_H (w : List ℤ) (u y : ℤ) :
    hydraIterate 3 2 [0, 1] w (u, y) = (3 * (u / 2) + u % 2, y + w.getD (u % 2).toNat 0) := by
  rcases Int.emod_two_eq_zero_or_one u with h | h <;> simp [hydraIterate, h]

/-! ## #323 is `A 1` -/

theorem hydra323_semiconj (p : ℤ × ℤ) :
    (fun q : ℤ × ℤ ↦ (q.1 - 2, q.2)) (hydraIterate 3 2 [0, 1] [2, -1] p) =
      hydraIterate 3 2 [1, 2] [2, -1] (p.1 - 2, p.2) := by
  obtain ⟨u, y⟩ := p
  rcases Int.emod_two_eq_zero_or_one u with h | h
  · have h' : (u - 2) % 2 = 0 := by omega
    simp only [hydraIterate, h, h', Int.toNat_zero, Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    simp only [List.getD_cons_zero]; omega
  · have h' : (u - 2) % 2 = 1 := by omega
    simp only [hydraIterate, h, h', Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    simp only [Int.toNat_one, List.getD_cons_succ, List.getD_cons_zero]; omega

/-- **int-y1's #323 is Antihydra's engine and walk, started at `2`** (`x + 2` follows `H`). -/
theorem hydra323_iff_A1 : hydra323 ↔ A 1 := by
  have key : ∀ n, ((hydraIterate 3 2 [1, 2] [2, -1])^[n] (1, 2)).2 =
      ((hydraIterate 3 2 [0, 1] [2, -1])^[n] (3, 2)).2 := fun n ↦
    hydra_transfer (fun q ↦ (q.1 - 2, q.2)) hydra323_semiconj (fun _ ↦ rfl) (3, 2) n
  unfold hydra323 A Hydra
  simp only [Nat.cast_ofNat, pow_one, key]
  constructor
  · intro h n
    cases n with
    | zero => simp
    | succ n =>
      rw [Function.iterate_succ_apply]
      have : hydraIterate 3 2 [0, 1] [2, -1] (2, 0) = (3, 2) := by decide
      rw [this]; exact h n
  · intro h n
    have := h (n + 1)
    rw [Function.iterate_succ_apply] at this
    have e : hydraIterate 3 2 [0, 1] [2, -1] (2, 0) = (3, 2) := by decide
    rwa [e] at this

/-! ## BB(2,5) Hydra is `H` from `3`, mirrored walk -/

theorem hydraBB25_semiconj (p : ℤ × ℤ) :
    (fun q : ℤ × ℤ ↦ (3 * q.1 - 6, q.2)) (hydraIterate 3 2 [0, 1] [-1, 2] p) =
      hydraIterate 3 2 [3, 3] [-1, 2] (3 * p.1 - 6, p.2) := by
  obtain ⟨u, y⟩ := p
  rcases Int.emod_two_eq_zero_or_one u with h | h
  · have h' : (3 * u - 6) % 2 = 0 := by omega
    simp only [hydraIterate, h, h', Int.toNat_zero, Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    simp only [List.getD_cons_zero]; omega
  · have h' : (3 * u - 6) % 2 = 1 := by omega
    simp only [hydraIterate, h, h', Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    simp only [Int.toNat_one, List.getD_cons_succ, List.getD_cons_zero]; omega

/-- **BB(2,5) Hydra is the `H`-orbit of `3` with the mirrored walk** (`−1` even, `+2` odd);
the conjugacy is `a = 3u − 6`. -/
theorem hydraBB25_iff : hydraBB25 ↔ Hydra 3 2 [0, 1] [-1, 2] (3, 0) := by
  have key : ∀ n, ((hydraIterate 3 2 [3, 3] [-1, 2])^[n] (3, 0)).2 =
      ((hydraIterate 3 2 [0, 1] [-1, 2])^[n] (3, 0)).2 := fun n ↦
    hydra_transfer (fun q ↦ (3 * q.1 - 6, q.2)) hydraBB25_semiconj (fun _ ↦ rfl) (3, 0) n
  unfold hydraBB25 Hydra
  simp only [Nat.cast_ofNat, key]

/-- The first coordinate of a `hydraIterate` step ignores the walk. -/
theorem hydraIterate_fst (p q : ℤ) (g w w' : List ℤ) (x y y' : ℤ) :
    (hydraIterate p q g w (x, y)).1 = (hydraIterate p q g w' (x, y')).1 := rfl

/-- **#323 and BB(2,5) Hydra run on one orbit**: after the conjugacies above, both are walks on
the parity sequence of `H^n(3)` (#323 with `+2/−1` from counter `2`, Hydra with `−1/+2` from `0`).
-/
theorem hydra323_hydraBB25_same_orbit (n : ℕ) :
    ((hydraIterate 3 2 [0, 1] [2, -1])^[n] (3, 2)).1 =
      ((hydraIterate 3 2 [0, 1] [-1, 2])^[n] (3, 0)).1 := by
  suffices ∀ p p' : ℤ × ℤ, p.1 = p'.1 →
      ((hydraIterate 3 2 [0, 1] [2, -1])^[n] p).1 =
        ((hydraIterate 3 2 [0, 1] [-1, 2])^[n] p').1 from this _ _ rfl
  induction n with
  | zero => intro p p' h; exact h
  | succ n ih =>
    intro p p' h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    apply ih
    obtain ⟨x, y⟩ := p; obtain ⟨x', y'⟩ := p'
    simp only at h; subst h
    exact hydraIterate_fst _ _ _ _ _ _ _ _

/-! ## Two halting starts on Antihydra's engine -/

/-- `A 0` halts at walk step 1. -/
theorem not_A0 : ¬ A 0 := by
  intro h
  have := h 1
  revert this
  decide

/-- `A 4` (start `16`) halts at walk step 22. -/
theorem not_A4 : ¬ A 4 := by
  intro h
  have := h 22
  revert this
  decide +kernel

/-! ## #218's engine is `K(u) = ⌊4u/3⌋` -/

theorem hydra218_semiconj (p : ℤ × ℤ) :
    (fun q : ℤ × ℤ ↦ (q.1 - 3, q.2)) (hydraIterate 4 3 [0, 1, 2] [3, 1, -1] p) =
      hydraIterate 4 3 [1, 2, 3] [3, 1, -1] (p.1 - 3, p.2) := by
  obtain ⟨u, y⟩ := p
  have h3 : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases h3 with h | h | h
  · have h' : (u - 3) % 3 = 0 := by omega
    simp only [hydraIterate, h, h', Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    simp; omega
  · have h' : (u - 3) % 3 = 1 := by omega
    simp only [hydraIterate, h, h', Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    simp; omega
  · have h' : (u - 3) % 3 = 2 := by omega
    simp only [hydraIterate, h, h', Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    simp; omega

/-- `hydraIterate 4 3 [0, 1, 2]` is `K(u) = ⌊4u/3⌋`. -/
theorem hydraIterate_K (w : List ℤ) (u y : ℤ) :
    (hydraIterate 4 3 [0, 1, 2] w (u, y)).1 = 4 * u / 3 := by
  have h3 : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases h3 with h | h | h <;> simp [hydraIterate, h] <;> omega

/-- **#218 is the `K`-orbit of `4`** with walk `[3, 1, −1]` on `u mod 3` (`x + 3` follows `K`). -/
theorem hydra218_iff : hydra218 ↔ Hydra 4 3 [0, 1, 2] [3, 1, -1] (4, 3) := by
  have key : ∀ n, ((hydraIterate 4 3 [1, 2, 3] [3, 1, -1])^[n] (1, 3)).2 =
      ((hydraIterate 4 3 [0, 1, 2] [3, 1, -1])^[n] (4, 3)).2 := fun n ↦
    hydra_transfer (fun q ↦ (q.1 - 3, q.2)) hydra218_semiconj (fun _ ↦ rfl) (4, 3) n
  unfold hydra218 Hydra
  simp only [Nat.cast_ofNat, key]

end Collatz.Census
