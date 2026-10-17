/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic
import Collatz.Census
import Collatz.Antihydra.Foils

/-!
# Rounding-choice foils for the whole Hydra schema

int-y1's `Hydra` schema (`Collatz.Bigfoot.Hydra`): `x ↦ p⌊x/q⌋ + g[x mod q]`, walk
`y ↦ y + w[x mod q]`, cryptid = "`y ≥ 0` forever".  T2 (`Collatz.Antihydra.Foils`) showed for
Antihydra that halting members of the rounding-choice family accumulate at the cryptid.  This
file lifts that gate to the schema.

**The family.**  A defect-`d` member adds a choice `τ x : Fin (d+1)` to the image:
`x ↦ p⌊x/q⌋ + g[x mod q] + τ x`, with the walk unchanged (`Sys.step`).  The original map is the
all-zero member (`Sys.step_zero`, `Sys.hydra_iff`).  The block subfamily `F_{L,d}` asks `τ` to be
constant on blocks of `qL` consecutive integers (`member q L σ`, block `x / (qL)`), as in T2.

**Results.**
* `Sys.halting_dense_of_drain`: the general gate.  A *drain certificate* (a trap predicate, a
  potential `Φ ≥ 0`, a multiplier `m`, and an entry predicate satisfied along the starting member's
  orbit) makes halting members dense in `F_{L,d}`: every member agrees, on all blocks `< K`, with a
  halting member.  Uses only expansion (`q < p`) and the certificate.
* `Sys.halting_dense_of_window`: the cyclic window condition (every `d+1` consecutive residues mod
  `q` meet a residue with `w < 0`) is a certificate, for every `p > q ≥ 1`.
* `Sys.window_two`: for `q = 2`, `d = 1`, any residue with `w < 0` gives the window condition.
* Instances: Antihydra, int-y1 #323, BB(2,5) Hydra (`q = 2`, `d = 1`), #218 (`d = 2`), Bigfoot.
* T2 agreement: T2's family is the odd-supported part of `F_{L,1}` for Antihydra's data, with the
  same halting predicate (`antihydra_t2_halts_iff`, `t2_member_emb`).
-/

namespace Collatz.HydraFoils

open Collatz.Bigfoot

/-- A system in int-y1's `Hydra` schema: slope `p/q`, geometric offsets `g`, walk offsets `w`. -/
structure Sys where
  p : ℕ
  q : ℕ
  g : List ℤ
  w : List ℤ

namespace Sys

variable (S : Sys)

/-- The residue index `x mod q` as `hydraIterate` reads its lists. -/
def res (x : ℤ) : ℕ := (x % (S.q : ℤ)).toNat

/-- The floor image `p⌊x/q⌋ + g[x mod q]`. -/
def img (x : ℤ) : ℤ := (S.p : ℤ) * (x / (S.q : ℤ)) + S.g.getD (S.res x) 0

/-- The walk increment `w[x mod q]` at value `x`. -/
def wt (x : ℤ) : ℤ := S.w.getD (S.res x) 0

/-- One step of the defect-`d` member with choice `τ`: the image gets `τ x ∈ [0, d]` added; the
walk is unchanged. -/
def step {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) : ℤ × ℤ :=
  (S.img s.1 + ((τ s.1 : ℕ) : ℤ), s.2 + S.wt s.1)

/-- The orbit of `s` under the member `τ`. -/
def orbit {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) (n : ℕ) : ℤ × ℤ := (S.step τ)^[n] s

/-- The member `τ` halts from `s`: the walk goes negative. -/
def Halts {d : ℕ} (τ : ℤ → Fin (d + 1)) (s : ℤ × ℤ) : Prop := ∃ n, (S.orbit τ s n).2 < 0

/-- **Faithfulness anchor.**  The all-zero member is int-y1's `hydraIterate`. -/
theorem step_zero (d : ℕ) :
    S.step (fun _ => (0 : Fin (d + 1))) = hydraIterate S.p S.q S.g S.w := by
  sorry

/-- **Faithfulness anchor.**  The cryptid `Hydra p q g w s` is "the all-zero member never
halts". -/
theorem hydra_iff (d : ℕ) (s : ℤ × ℤ) :
    Hydra S.p S.q S.g S.w s ↔ ¬ S.Halts (fun _ => (0 : Fin (d + 1))) s := by
  sorry

end Sys

/-- Block index of a value: blocks of `qL` consecutive integers. -/
def blk (q L : ℕ) (x : ℤ) : ℤ := x / ((q * L : ℕ) : ℤ)

/-- The member of `F_{L,d}` with block choices `σ`. -/
def member (q L : ℕ) {d : ℕ} (σ : ℤ → Fin (d + 1)) : ℤ → Fin (d + 1) := fun x => σ (blk q L x)

theorem member_zero (q L d : ℕ) :
    member q L (fun _ => (0 : Fin (d + 1))) = fun _ => 0 := rfl

namespace Sys

variable (S : Sys)

/-- **The general gate.**  A drain certificate for defect `d` makes halting members dense in
`F_{L,d}`.  The certificate: a trap predicate that some choice keeps, along which the potential
`m y + Φ x` falls by at least one per step; an entry predicate `Ent` from which some choice enters
the trap, holding along the orbit of the starting member `σ₀`; and strict growth at `Ent` values
above the start.  Then some member agreeing with `σ₀` on every block `< K` halts from `s`. -/
theorem halting_dense_of_drain (hq : 0 < S.q) (hpq : S.q < S.p) {d L : ℕ} (hL : 1 ≤ L)
    (Ent Trap : ℤ → Prop) (Φ : ℤ → ℕ) (m : ℕ)
    (htrap : ∀ x, Trap x → ∃ c : Fin (d + 1),
      Trap (S.img x + (c : ℕ)) ∧ (m : ℤ) * S.wt x + Φ (S.img x + (c : ℕ)) + 1 ≤ Φ x)
    (hent : ∀ x, Ent x → ∃ c : Fin (d + 1), Trap (S.img x + (c : ℕ)))
    (σ₀ : ℤ → Fin (d + 1)) (K : ℤ) (s : ℤ × ℤ)
    (horig : ∀ n, Ent (S.orbit (member S.q L σ₀) s n).1)
    (hesc : ∀ x, s.1 ≤ x → Ent x → x + 1 ≤ S.img x) :
    ∃ σ : ℤ → Fin (d + 1), (∀ b < K, σ b = σ₀ b) ∧ S.Halts (member S.q L σ) s := by
  sorry

/-- The cyclic window condition: every `d + 1` consecutive residues mod `q` contain one with
`w < 0`. -/
def Window (d : ℕ) : Prop := ∀ a < S.q, ∃ c ≤ d, S.w.getD ((a + c) % S.q) 0 < 0

/-- **Window gate.**  For every `p > q ≥ 1`, the window condition at defect `d` makes halting
members dense in `F_{L,d}` from any start above which the image grows. -/
theorem halting_dense_of_window (hq : 0 < S.q) (hpq : S.q < S.p) {d L : ℕ} (hL : 1 ≤ L)
    (hW : S.Window d) (σ₀ : ℤ → Fin (d + 1)) (K : ℤ) (s : ℤ × ℤ)
    (hesc : ∀ x, s.1 ≤ x → x + 1 ≤ S.img x) :
    ∃ σ : ℤ → Fin (d + 1), (∀ b < K, σ b = σ₀ b) ∧ S.Halts (member S.q L σ) s := by
  sorry

/-- For `q = 2`, `d = 1`: any residue with `w < 0` gives the window condition. -/
theorem window_two (h2 : S.q = 2) {r : ℕ} (hr : r < 2) (hw : S.w.getD r 0 < 0) :
    S.Window 1 := by
  sorry

end Sys

end Collatz.HydraFoils
