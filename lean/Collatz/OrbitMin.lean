import Collatz.Basic
import Collatz.Conjecture
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Nat.Lattice

/-!
# The orbit minimum `colMin`

Tao 2019 (arXiv:1909.03562) defines

```
Colmin(N) := inf_{n ∈ ℕ} Col^n(N)
```

as the minimum element of the forward Collatz orbit. We define
`colMin n := sInf {T^[k] n | k : ℕ}` and prove the basic facts:
membership in the orbit, lower bound on iterates, equivalence of the
Collatz conjecture with "every positive integer has `colMin = 1`".

For `n = 0`, `colMin 0 = 0`. For `n ≥ 1`, `colMin n ≥ 1`.
-/

namespace Collatz

/-- The forward Collatz orbit of `n` as a set. -/
def orbit (n : ℕ) : Set ℕ := Set.range (fun k => T^[k] n)

@[simp] lemma iterate_mem_orbit (n k : ℕ) : T^[k] n ∈ orbit n :=
  ⟨k, rfl⟩

@[simp] lemma self_mem_orbit (n : ℕ) : n ∈ orbit n :=
  ⟨0, by simp⟩

lemma orbit_nonempty (n : ℕ) : (orbit n).Nonempty :=
  ⟨n, self_mem_orbit n⟩

/-- The orbit minimum: `colMin(N) := inf {T^k(N) : k ∈ ℕ}`. -/
noncomputable def colMin (n : ℕ) : ℕ := sInf (orbit n)

lemma colMin_le_iterate (n k : ℕ) : colMin n ≤ T^[k] n :=
  Nat.sInf_le (iterate_mem_orbit n k)

lemma colMin_le_self (n : ℕ) : colMin n ≤ n :=
  Nat.sInf_le (self_mem_orbit n)

lemma colMin_mem_orbit (n : ℕ) : colMin n ∈ orbit n :=
  Nat.sInf_mem (orbit_nonempty n)

/-- A single `T`-step preserves positivity. -/
lemma one_le_T (m : ℕ) (h : 1 ≤ m) : 1 ≤ T m := by
  unfold T
  by_cases hev : m % 2 = 0
  · rw [if_pos hev]
    -- m ≥ 1 and even ⇒ m ≥ 2 ⇒ m / 2 ≥ 1
    omega
  · rw [if_neg hev]
    -- m ≥ 1 odd ⇒ 3m + 1 ≥ 4 ≥ 1
    omega

/-- For `n ≥ 1`, every iterate `T^[k] n` is also `≥ 1`. -/
lemma one_le_iterate (n : ℕ) (h : 1 ≤ n) (k : ℕ) : 1 ≤ T^[k] n := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact one_le_T _ ih

/-- For `n ≥ 1`, `colMin n ≥ 1`. -/
lemma one_le_colMin_of_one_le (n : ℕ) (h : 1 ≤ n) : 1 ≤ colMin n := by
  rcases colMin_mem_orbit n with ⟨k, hk⟩
  -- hk : (fun k => T^[k] n) k = colMin n, i.e., T^[k] n = colMin n
  rw [← hk]
  exact one_le_iterate n h k

@[simp] lemma colMin_zero : colMin 0 = 0 :=
  le_antisymm (colMin_le_self 0) (Nat.zero_le _)

@[simp] lemma colMin_one : colMin 1 = 1 :=
  le_antisymm (colMin_le_self 1) (one_le_colMin_of_one_le 1 le_rfl)

/-- The Collatz conjecture, restated using `colMin`: every positive
integer has orbit minimum `1`. -/
theorem conjecture_iff_colMin_one :
    Conjecture ↔ ∀ n, 1 ≤ n → colMin n = 1 := by
  constructor
  · intro hConj n hn
    obtain ⟨k, hk⟩ := hConj n hn
    apply le_antisymm
    · calc colMin n ≤ T^[k] n := colMin_le_iterate n k
        _ = 1 := hk
    · exact one_le_colMin_of_one_le n hn
  · intro hMin n hn
    rcases colMin_mem_orbit n with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    -- hk : (fun k => T^[k] n) k = colMin n
    -- want: T^[k] n = 1
    rw [show T^[k] n = colMin n from hk, hMin n hn]

end Collatz
