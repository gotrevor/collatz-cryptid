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
  sorry

/-- After any step from a state with `c ≥ 1`, `b' ≡ c + 1 (mod 2)`. -/
theorem step_b_parity (s t : Dyn) (hc : 1 ≤ s.c) (h : step s = some t) :
    t.b % 2 = (s.c + 1) % 2 := by
  sorry

/-- **Two steps flip the parity of `b`**, from any state. -/
theorem step_step_parity (s t u : Dyn) (h₁ : step s = some t) (h₂ : step t = some u) :
    u.b % 2 = (s.b + 1) % 2 := by
  sorry

/-- **The parity clock** (kickoff form): along the orbit, `b_{n+2} ≡ b_n + 1 (mod 2)`. -/
theorem parity_clock (n : ℕ) (s₀ s₂ : Dyn) (h₂ : orbit (n + 2) = some s₂)
    (h₀ : orbit n = some s₀) : s₂.b % 2 = (s₀.b + 1) % 2 := by
  sorry

/-- The clock read off from `init`: `b_n` is odd iff `n ≡ 0, 1 (mod 4)`. -/
theorem orbit_b_mod_two (n : ℕ) (s : Dyn) (h : orbit n = some s) :
    s.b % 2 = if n % 4 < 2 then 1 else 0 := by
  sorry

/-- The third coordinate along the orbit: `c = 2` at phases `0, 3`, and `c ∈ {3, 5}` at
phases `1, 2`. -/
theorem orbit_c_phase (n : ℕ) (s : Dyn) (h : orbit n = some s) :
    (n % 4 = 0 ∨ n % 4 = 3 → s.c = 2) ∧ (n % 4 = 1 ∨ n % 4 = 2 → s.c = 3 ∨ s.c = 5) := by
  sorry

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
  sorry

/-- Bigfoot's halt branch is exactly the walk stepping to `-1`. -/
theorem hydraIterate_X_none (s : Dyn) (hc : s.c = 2 ∨ s.c = 3 ∨ s.c = 5) (h : step s = none) :
    (hydraIterate 32 24 bigfootH bigfootW (X s, s.a)).2 = -1 := by
  sorry

/-- **Bigfoot is `Hydra 32 24 bigfootH bigfootW (10, 2)`.**  Bigfoot's `Dyn` orbit never halts
iff int-y1's `Hydra` predicate holds for this data (`X(init) = 4·1 + 3·2 = 10`, `a(init) = 2`).
`∀ n, orbit n ≠ none` is `BigfootHypothesisArith` by `BigfootHypothesisArith_iff`
(`Classification.lean`). -/
theorem nonhalt_iff_hydra :
    (∀ n, orbit n ≠ none) ↔ Hydra 32 24 bigfootH bigfootW (10, 2) := by
  sorry

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

/-- **The block map.**  From a phase-0 state (`b` odd, `c = 2`) with `a ≥ 2`, four steps act as
`(a, 162q + r, 2) ↦ (a + w₄[r], 512q + g₄[r], 2)`: slope `(4/3)⁴ = 256/81` on base-3 cylinders. -/
theorem step4_block (A q r : ℕ) (hr : r < 162) (hodd : r % 2 = 1) :
    ∃ t : Dyn, step4 ⟨A + 2, 162 * q + r, 2⟩ = some t ∧ t.c = 2 ∧
      t.b = 512 * q + blockG.getD (r / 2) 0 ∧
      (t.a : ℤ) = A + 2 + blockW.getD (r / 2) 0 := by
  sorry

/-- **Drift `+1/6` per step.**  The block walk sums to `54` over the `81` odd residues mod `162`:
mean `+2/3` per 4-step block under the uniform distribution of `b mod 162`. -/
theorem blockW_sum : blockW.sum = 54 ∧ blockW.length = 81 := by
  sorry

end Dyn

end Collatz.Bigfoot
