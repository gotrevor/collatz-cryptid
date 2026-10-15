/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic
import Collatz.Bigfoot.Dynamics

/-!
# Bigfoot's parity clock, and Bigfoot as a `Hydra`

Three exact facts about Ligocki's `(a, b, c)` dynamics `Dyn.step` (`Dynamics.lean`).

1. **The parity clock** (`Dyn.parity_clock`, `Dyn.orbit_b_mod_two`).  Every branch adds an odd
   constant to `8k + c`, so `b' ≡ c + 1 (mod 2)`; and the new `c` is `2` after an even residue,
   `3` or `5` after an odd one, so `c' ≡ b (mod 2)`.  Hence `b_{n+2} ≡ b_n + 1 (mod 2)` along any
   run of two steps.  From `init = (2, 1, 2)` the parity of `b_n` is `1, 1, 0, 0, 1, 1, 0, 0, …`:
   a deterministic 4-phase clock.  All of the mixing lives in `b mod 3`.  At phases `0` and `3`
   (`n ≡ 0, 3 mod 4`) the third coordinate is pinned to `c = 2` (`Dyn.orbit_c_phase`).

2. **Bigfoot is a `Hydra` in int-y1's schema** (`Dyn.nonhalt_iff_hydra`).  In the coordinate
   `X = 4b + 3c` the `c`-dependence cancels: `X ↦ 32 ⌊X / 24⌋ + h[X mod 24]` (slope `4/3`), with the
   counter `a ↦ a + w[X mod 24]`, and Bigfoot's halt branch is exactly "the counter goes to `-1`".
   So Bigfoot's non-halting is `Hydra 32 24 bigfootH bigfootW (10, 2)`, where `Hydra` is the
   schema of int-y1's `BBfLean/Cryptid.lean` (restated here verbatim as `Bigfoot.Hydra`).

3. **The clocked block map** (`Dyn.step4_block`).  Started at phase `0` (`b` odd, `c = 2`) with
   `a ≥ 2`, four steps send `(a, 162q + r, 2)` to `(a + w₄[r], 512q + g₄[r], 2)`.  The slope is
   `256/81 = (4/3)⁴`: Bigfoot is a base-3 `×4/3` map driven by a 4-phase parity clock.  The block
   walk `w₄` sums to `54` over the `81` odd residues (`blockW_sum`), i.e. mean `+2/3` per block,
   `+1/6` per step under the uniform (Haar) distribution of `b mod 162`.
   **Prior work:** this block map is LegionMammal978's `C(a, 81k + r) → C(a + Δa, 256k + s)`,
   `C(a, β) = A(a, 4β + 1, 2)` (`bigfoot-sim`, 2023); `step4_legion` checks his table verbatim.
   The clock is implicit in his representation (a `c = 2` state every fourth step).

None of this settles Bigfoot: (2) and (3) are exact *reformulations*, and the open content is still
whether the counter stays nonnegative along one specific orbit (a single-orbit residue-frequency
statement, the same wall as Antihydra's).
-/

namespace Collatz.Bigfoot

/-! ## int-y1's `Hydra` schema

Transcribed verbatim (names camel-cased) from int-y1's `proofs/BBfLean/Cryptid.lean`
(`hydra_iterate`, `Hydra`): `x ↦ p ⌊x/q⌋ + g[x mod q]`, `y ↦ y + w[x mod q]`, and the cryptid
holds iff `y ≥ 0` forever.  Integer division here is Lean's `Int` `/` and `%` (Euclidean), as there.
-/

/-- One step of int-y1's `hydra_iterate`. -/
def hydraIterate (rNum rDen : ℤ) (geoOffset walkOffset : List ℤ) : ℤ × ℤ → ℤ × ℤ :=
  fun init ↦ match init with
  | (x, y) => (rNum * (x / rDen) + geoOffset.getD (x % rDen).toNat 0,
      y + walkOffset.getD (x % rDen).toNat 0)

/-- int-y1's `Hydra` predicate: the walk coordinate stays nonnegative forever. -/
def Hydra (rNum rDen : ℕ) (geoOffset walkOffset : List ℤ) (init : ℤ × ℤ) : Prop :=
  ∀ n : ℕ, ((hydraIterate rNum rDen geoOffset walkOffset)^[n] init).2 ≥ 0

namespace Dyn

/-! ## 1. The parity clock -/

/-- After any step the third coordinate is in `{2, 3, 5}` and has the parity of the old `b`. -/
theorem step_c (s t : Dyn) (h : step s = some t) :
    (t.c = 2 ∨ t.c = 3 ∨ t.c = 5) ∧ t.c % 2 = s.b % 2 := by
  obtain ⟨a, b, c⟩ := s
  dsimp only [step] at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h) <;> subst h <;>
    (try norm_num) <;> omega

/-- After any step from a state with `c ≥ 1`, `b' ≡ c + 1 (mod 2)`. -/
theorem step_b_parity (s t : Dyn) (hc : 1 ≤ s.c) (h : step s = some t) :
    t.b % 2 = (s.c + 1) % 2 := by
  obtain ⟨a, b, c⟩ := s
  simp only at hc
  dsimp only [step] at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h) <;> subst h <;>
    (try norm_num) <;> omega

/-- **Two steps flip the parity of `b`**, from any state. -/
theorem step_step_parity (s t u : Dyn) (h₁ : step s = some t) (h₂ : step t = some u) :
    u.b % 2 = (s.b + 1) % 2 := by
  have h₁' := step_c s t h₁
  have h₂' := step_b_parity t u (by omega) h₂
  omega

/-- A reached state has a reached predecessor that steps to it. -/
theorem orbit_succ (n : ℕ) (s : Dyn) (h : orbit (n + 1) = some s) :
    ∃ s', orbit n = some s' ∧ step s' = some s := by
  change (orbit n).bind step = some s at h
  exact Option.bind_eq_some_iff.mp h

/-- **The parity clock** (kickoff form): along the orbit, `b_{n+2} ≡ b_n + 1 (mod 2)`. -/
theorem parity_clock (n : ℕ) (s₀ s₂ : Dyn) (h₂ : orbit (n + 2) = some s₂)
    (h₀ : orbit n = some s₀) : s₂.b % 2 = (s₀.b + 1) % 2 := by
  obtain ⟨s₁, h₁, e₂⟩ := orbit_succ _ _ h₂
  obtain ⟨s₀', h₀', e₁⟩ := orbit_succ _ _ h₁
  rw [h₀] at h₀'
  cases h₀'
  exact step_step_parity _ _ _ e₁ e₂

/-- The clock read off from `init`: `b_n` is odd iff `n ≡ 0, 1 (mod 4)`. -/
theorem orbit_b_mod_two (n : ℕ) (s : Dyn) (h : orbit n = some s) :
    s.b % 2 = if n % 4 < 2 then 1 else 0 := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    match n, h with
    | 0, h => cases h; rfl
    | 1, h => cases h; rfl
    | n + 2, h =>
      obtain ⟨s₁, h₁, -⟩ := orbit_succ _ _ h
      obtain ⟨s₀, h₀, -⟩ := orbit_succ _ _ h₁
      have := ih n (by omega) s₀ h₀
      have := parity_clock n s₀ s h h₀
      split_ifs at * <;> omega

/-- The third coordinate along the orbit: `c = 2` at phases `0, 3`, and `c ∈ {3, 5}` at
phases `1, 2`. -/
theorem orbit_c_phase (n : ℕ) (s : Dyn) (h : orbit n = some s) :
    (n % 4 = 0 ∨ n % 4 = 3 → s.c = 2) ∧ (n % 4 = 1 ∨ n % 4 = 2 → s.c = 3 ∨ s.c = 5) := by
  match n, h with
  | 0, h => cases h; exact ⟨fun _ ↦ rfl, by omega⟩
  | n + 1, h =>
    obtain ⟨s', h', e⟩ := orbit_succ _ _ h
    have hc := step_c s' s e
    have hb := orbit_b_mod_two n s' h'
    split_ifs at hb <;> constructor <;> intro <;> omega

/-! ## 2. Bigfoot as int-y1's `Hydra 32 24` -/

/-- The conjugating coordinate `X = 4b + 3c`. -/
def X (s : Dyn) : ℤ := 4 * s.b + 3 * s.c

/-- Geometric offsets of Bigfoot in the `X` coordinate (`X ↦ 32 ⌊X/24⌋ + h[X mod 24]`).
Residues `≡ 0 (mod 4)` are unreachable (`X ≡ 3c (mod 4)`, `c ∈ {2,3,5}`) and carry `0`. -/
def bigfootH : List ℤ :=
  [0, -2, 5, 7, 0, 9, 10, 6, 0, 14, 13, 17, 0, 17, 26, 22, 0, 30, 27, 25, 0, 31, 26, 38]

/-- Walk offsets of Bigfoot in the `X` coordinate: the change of `a`. -/
def bigfootW : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, -1, 0, 0, -1, 0, 1, 0, 0, 1, -1]

/-- One Bigfoot step is one `hydraIterate 32 24` step on `(X, a)`, for `c ∈ {2, 3, 5}`. -/
theorem hydraIterate_X (s t : Dyn) (hc : s.c = 2 ∨ s.c = 3 ∨ s.c = 5) (h : step s = some t) :
    hydraIterate 32 24 bigfootH bigfootW (X s, s.a) = (X t, (t.a : ℤ)) := by
  obtain ⟨a, b, c⟩ := s
  simp only at hc
  unfold hydraIterate X
  have h24 : 0 ≤ (4 * (b : ℤ) + 3 * c) % 24 := by omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, (4 * (b : ℤ) + 3 * c) % 24 = ρ :=
    ⟨_, (Int.toNat_of_nonneg h24).symm⟩
  have hρ24 : ρ < 24 := by omega
  simp only [hρ, Int.toNat_natCast]
  dsimp only [step] at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h) <;> subst h <;>
    interval_cases ρ <;> first | omega | (simp [bigfootH, bigfootW]; omega)

/-- `step` halts only on `b ≡ 2 (mod 6)`, `a = 0` (as `Dyn.step_eq_none_iff` in
`Classification.lean`, re-proved here to keep this file's imports light). -/
theorem step_eq_none_iff' (s : Dyn) : step s = none ↔ s.b % 6 = 2 ∧ s.a = 0 := by
  obtain ⟨a, b, c⟩ := s
  dsimp only [step]
  split_ifs <;> simp_all

/-- The third coordinate is in `{2, 3, 5}` all along the orbit. -/
theorem orbit_c_mem (n : ℕ) (s : Dyn) (h : orbit n = some s) : s.c = 2 ∨ s.c = 3 ∨ s.c = 5 := by
  match n, h with
  | 0, h => cases h; simp [init]
  | n + 1, h =>
    obtain ⟨s', -, e⟩ := orbit_succ _ _ h
    exact (step_c s' s e).1

/-- Along the orbit, the `Hydra` iterate is `(X, a)`. -/
theorem hydra_iterate_orbit (n : ℕ) (s : Dyn) (h : orbit n = some s) :
    (hydraIterate 32 24 bigfootH bigfootW)^[n] (10, 2) = (X s, (s.a : ℤ)) := by
  induction n generalizing s with
  | zero => cases h; rfl
  | succ n ih =>
    obtain ⟨s', h', e⟩ := orbit_succ _ _ h
    rw [Function.iterate_succ_apply', ih s' h']
    exact hydraIterate_X s' s (orbit_c_mem n s' h') e

/-- Bigfoot's halt branch is exactly the walk stepping to `-1`. -/
theorem hydraIterate_X_none (s : Dyn) (hc : s.c = 2 ∨ s.c = 3 ∨ s.c = 5) (h : step s = none) :
    (hydraIterate 32 24 bigfootH bigfootW (X s, s.a)).2 = -1 := by
  obtain ⟨a, b, c⟩ := s
  simp only at hc
  have h' := (step_eq_none_iff' _).mp h
  simp only at h'
  unfold hydraIterate X
  have h24 : 0 ≤ (4 * (b : ℤ) + 3 * c) % 24 := by omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, (4 * (b : ℤ) + 3 * c) % 24 = ρ :=
    ⟨_, (Int.toNat_of_nonneg h24).symm⟩
  have hρ24 : ρ < 24 := by omega
  simp only [hρ, Int.toNat_natCast]
  interval_cases ρ <;> first | omega | simp [bigfootW, h'.2]

/-- **Bigfoot is `Hydra 32 24 bigfootH bigfootW (10, 2)`.**  Bigfoot's `Dyn` orbit never halts
iff int-y1's `Hydra` predicate holds for this data (`X(init) = 4·1 + 3·2 = 10`, `a(init) = 2`).
`∀ n, orbit n ≠ none` is `BigfootHypothesisArith` by `BigfootHypothesisArith_iff`
(`Classification.lean`). -/
theorem nonhalt_iff_hydra :
    (∀ n, orbit n ≠ none) ↔ Hydra 32 24 bigfootH bigfootW (10, 2) := by
  simp only [Hydra, Nat.cast_ofNat]
  constructor
  · intro hn n
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (hn n)
    rw [hydra_iterate_orbit n s hs]
    simp
  · intro hy n
    induction n with
    | zero => simp [orbit]
    | succ n ih =>
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp ih
      intro hnone
      have hstep : step s = none := by
        change (orbit n).bind step = none at hnone
        rwa [hs, Option.bind_some] at hnone
      have := hy (n + 1)
      rw [Function.iterate_succ_apply', hydra_iterate_orbit n s hs,
        hydraIterate_X_none s (orbit_c_mem n s hs) hstep] at this
      omega

/-! ## 3. The clocked block map -/

/-- Four steps of `Dyn.step`. -/
def step4 (s : Dyn) : Option Dyn :=
  ((step s).bind step |>.bind step).bind step

/-- `g₄[i]` for the odd residue `r = 2i + 1 (mod 162)`: `b ↦ 512 ⌊b/162⌋ + g₄[r]`. -/
def blockG : List ℕ :=
  [9, 17, 21, 29, 37, 45, 45, 53, 61, 61, 77, 77, 85, 93, 97, 105, 109, 117, 121, 129, 137, 141,
    149, 157, 157, 169, 173, 181, 189, 189, 197, 205, 213, 217, 221, 233, 233, 245, 249, 257, 265,
    269, 277, 281, 285, 293, 301, 309, 309, 317, 325, 329, 341, 345, 349, 357, 361, 369, 377, 385,
    389, 393, 405, 405, 417, 421, 429, 437, 437, 445, 453, 457, 461, 469, 477, 481, 489, 497, 501,
    509, 517]

/-- `w₄[i]` for the odd residue `r = 2i + 1 (mod 162)`: the change of `a` over the block. -/
def blockW : List ℤ :=
  [1, 0, 1, 0, -1, -2, 2, 1, 0, 4, -2, 2, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, -1, 3, 0, 1, 0, -1,
    3, 2, 1, 0, 1, 3, -1, 3, 0, 1, 0, -1, 0, -1, 1, 2, 1, 0, -1, 3, 2, 1, 2, -1, 0, 2, 1, 2, 1, 0,
    -1, 0, 2, -2, 2, -1, 0, -1, -2, 2, 1, 0, 1, 3, 2, 1, 2, 1, 0, 1, 1, -1]

/-- **Translation symmetry of one step**: adding `A` to `a` and `6m` to `b` adds `A` to `a'` and
`8m` to `b'` (for `c ≥ 1`).  This is what makes the block map affine in `⌊b/162⌋`. -/
theorem step_shift (s t : Dyn) (A m : ℕ) (hc : 1 ≤ s.c) (h : step s = some t) :
    step ⟨s.a + A, s.b + 6 * m, s.c⟩ = some ⟨t.a + A, t.b + 8 * m, t.c⟩ := by
  obtain ⟨a, b, c⟩ := s
  simp only at hc ⊢
  have hmod : (b + 6 * m) % 6 = b % 6 := by omega
  have hdiv : (b + 6 * m) / 6 = b / 6 + m := by omega
  dsimp only [step] at h ⊢
  rw [hmod, hdiv]
  split_ifs at h ⊢ <;> (simp only [Option.some.injEq] at h ⊢) <;> subst h <;>
    (try simp only [Dyn.mk.injEq]) <;>
    first | omega | (refine ⟨?_, ?_, ?_⟩ <;> first | trivial | omega)

/-- The concrete block check at residue `2i + 1`, base `a = 2`. -/
def blockOk (i : ℕ) : Bool :=
  (step4 ⟨2, 2 * i + 1, 2⟩).map (fun t => ((t.a : ℤ), t.b, t.c)) ==
    some (2 + blockW.getD i 0, blockG.getD i 0, 2)

theorem blockOk_all : (List.range 81).all blockOk = true := by decide +kernel

/-- The 81 concrete block runs, from `(2, 2i + 1, 2)`. -/
theorem step4_concrete (i : ℕ) (hi : i < 81) :
    (step4 ⟨2, 2 * i + 1, 2⟩).map (fun t => ((t.a : ℤ), t.b, t.c)) =
      some (2 + blockW.getD i 0, blockG.getD i 0, 2) := by
  have := List.all_eq_true.mp blockOk_all i (List.mem_range.mpr hi)
  simpa [blockOk] using this

/-- Translation symmetry of a block: adding `A` to `a` and `162m` to `b` adds `A` to `a'` and
`512m` to `b'` (for `c ≥ 1`). -/
theorem step4_shift (s t : Dyn) (A m : ℕ) (hc : 1 ≤ s.c) (h : step4 s = some t) :
    step4 ⟨s.a + A, s.b + 162 * m, s.c⟩ = some ⟨t.a + A, t.b + 512 * m, t.c⟩ := by
  simp only [step4, Option.bind_eq_some_iff] at h
  obtain ⟨t3, ⟨t2, ⟨t1, h1, h2⟩, h3⟩, h4⟩ := h
  have c1 := (step_c _ _ h1).1
  have c2 := (step_c _ _ h2).1
  have c3 := (step_c _ _ h3).1
  have e1 := step_shift _ _ A (27 * m) hc h1
  have e2 := step_shift _ _ A (36 * m) (by omega) h2
  have e3 := step_shift _ _ A (48 * m) (by omega) h3
  have e4 := step_shift _ _ A (64 * m) (by omega) h4
  rw [show 8 * (27 * m) = 6 * (36 * m) by ring] at e1
  rw [show 8 * (36 * m) = 6 * (48 * m) by ring] at e2
  rw [show 8 * (48 * m) = 6 * (64 * m) by ring] at e3
  rw [show 8 * (64 * m) = 512 * m by ring] at e4
  rw [show 162 * m = 6 * (27 * m) by ring]
  simp only [step4, e1, e2, e3, e4, Option.bind_some]

/-- **The block map.**  From a phase-0 state (`b` odd, `c = 2`) with `a ≥ 2`, four steps act as
`(a, 162q + r, 2) ↦ (a + w₄[r], 512q + g₄[r], 2)`: slope `(4/3)⁴ = 256/81` on base-3 cylinders. -/
theorem step4_block (A q r : ℕ) (hr : r < 162) (hodd : r % 2 = 1) :
    ∃ t : Dyn, step4 ⟨A + 2, 162 * q + r, 2⟩ = some t ∧ t.c = 2 ∧
      t.b = 512 * q + blockG.getD (r / 2) 0 ∧
      (t.a : ℤ) = A + 2 + blockW.getD (r / 2) 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, r = 2 * i + 1 := ⟨r / 2, by omega⟩
  have hi : i < 81 := by omega
  rw [show (2 * i + 1) / 2 = i by omega]
  obtain ⟨t, h4, ht⟩ := Option.map_eq_some_iff.mp (step4_concrete i hi)
  simp only [Prod.mk.injEq] at ht
  obtain ⟨ha, hb, hc⟩ := ht
  have e := step4_shift _ _ A q (by simp) h4
  simp only at e
  refine ⟨⟨t.a + A, t.b + 512 * q, t.c⟩, ?_, hc, by simp only; rw [hb]; ring,
    by simp only; push_cast; linarith⟩
  rw [← e]
  congr 2 <;> omega

/-- LegionMammal978's table (`bigfoot-sim`, `src/main.rs`, `TABLE`, 2023), transcribed verbatim:
entry `r` is `(Δa, s)` for `C(a, 81k + r) → C(a + Δa, 256k + s)`, where `C(a, β) = A(a, 4β + 1, 2)`.
-/
def legionTable : List (ℤ × ℕ) :=
  [(1, 2), (1, 5), (-1, 9), (2, 11), (0, 15), (-2, 19), (1, 21), (1, 24),
    (2, 27), (2, 30), (0, 34), (0, 37), (3, 39), (1, 43), (-1, 47), (2, 49),
    (0, 53), (3, 55), (3, 58), (1, 62), (-1, 66), (-1, 69), (2, 71), (0, 75),
    (3, 77), (1, 81), (-1, 85), (2, 87), (2, 90), (0, 94), (0, 97), (-2, 101),
    (-1, 104), (-1, 107), (2, 109), (0, 113), (3, 115), (1, 119), (1, 122),
    (1, 125), (-1, 129), (0, 132), (0, 135), (-2, 139), (1, 141), (4, 143),
    (2, 147), (0, 151), (0, 154), (0, 157), (1, 160), (1, 163), (-1, 167),
    (0, 170), (0, 173), (3, 175), (1, 179), (1, 182), (-1, 186), (0, 189),
    (0, 192), (0, 195), (1, 198), (1, 201), (-1, 205), (2, 207), (2, 210),
    (0, 214), (1, 217), (1, 220), (-1, 224), (2, 226), (2, 229), (0, 233),
    (-2, 237), (1, 239), (1, 242), (2, 245), (2, 248), (0, 252), (1, 255)]

/-- The concrete check of `legionTable` at residue `r`, base `a = 2`. -/
def legionOk (r : ℕ) : Bool :=
  (step4 ⟨2, 4 * r + 1, 2⟩).map (fun t => ((t.a : ℤ), t.b, t.c)) ==
    some (2 + (legionTable.getD r (0, 0)).1, 4 * (legionTable.getD r (0, 0)).2 + 1, 2)

theorem legionOk_all : (List.range 81).all legionOk = true := by decide +kernel

/-- **Cross-check against a primary source.**  LegionMammal978's reduced map
`C(a, 81k + r) → C(a + Δa, 256k + s)`, with `C(a, β) = A(a, 4β + 1, 2)`, is four steps of
`Dyn.step` for `a ≥ 2`.  (`(A + 2, 4(81k + r) + 1, 2)` is a phase-0 state: odd `b`, `c = 2`.) -/
theorem step4_legion (A k r : ℕ) (hr : r < 81) :
    ∃ t : Dyn, step4 ⟨A + 2, 4 * (81 * k + r) + 1, 2⟩ = some t ∧ t.c = 2 ∧
      t.b = 4 * (256 * k + (legionTable.getD r (0, 0)).2) + 1 ∧
      (t.a : ℤ) = A + 2 + (legionTable.getD r (0, 0)).1 := by
  have hc := List.all_eq_true.mp legionOk_all r (List.mem_range.mpr hr)
  simp only [legionOk, beq_iff_eq] at hc
  obtain ⟨t, h4, ht⟩ := Option.map_eq_some_iff.mp hc
  simp only [Prod.mk.injEq] at ht
  obtain ⟨ha, hb, hc⟩ := ht
  have e := step4_shift _ _ A (2 * k) (by simp) h4
  simp only at e
  refine ⟨⟨t.a + A, t.b + 512 * (2 * k), t.c⟩, ?_, hc, by simp only; rw [hb]; ring,
    by simp only; push_cast; linarith⟩
  rw [← e]
  congr 2 <;> omega

/-- **Drift `+1/6` per step.**  The block walk sums to `54` over the `81` odd residues mod `162`:
mean `+2/3` per 4-step block under the uniform distribution of `b mod 162`. -/
theorem blockW_sum : blockW.sum = 54 ∧ blockW.length = 81 := by decide +kernel

end Dyn

end Collatz.Bigfoot
