/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.HydraFoils

/-!
# Bigfoot drains at defect 2: one digit of lookahead

The residue-level certificate for Bigfoot needs defect `7` (`bigfoot_drift`), and no
residue-level certificate exists at `d ≤ 6` [computed].  But the image `32 ⌊X/24⌋ + h` mod `24`
depends on `⌊X/24⌋` only mod `3` (as `32 ≡ 0 (mod 8)`), so a steering that knows `X mod 72`
knows the next residue exactly, and the adversary only picks the base-3 digit after it.  On
`X mod 72` the energy game is won at defect `2`: a potential `φ ≤ 10` on `X mod 72` with, at
every `X mod 216`, a choice `c ≤ 2` along which `5 w + φ` falls by one.  The check is over
`216` residues (`X mod 216` fixes the image mod `72`: `72 ∣ 32 · 9`), by `decide +kernel`.
Found by value iteration (`sim/hydra_foils/energy.js 32 24 … 72 3 2 5`).
-/

namespace Collatz.HydraFoils

/-- The defect-2 potential on `X mod 72`. -/
def bigfootφ72 : List ℕ :=
  [5, 6, 4, 2, 5, 5, 3, 9, 5, 1, 6, 1, 5, 6, 0, 1, 5, 0, 3, 8, 5, 2, 8, 0, 2, 9, 1, 1, 2, 1, 4,
    6, 2, 1, 6, 3, 2, 8, 0, 4, 2, 0, 3, 10, 2, 1, 8, 0, 1, 6, 1, 1, 1, 3, 3, 6, 1, 4, 9, 5, 1, 10,
    0, 1, 1, 0, 3, 6, 1, 1, 9, 0]

/-- The defect-2 certificate, in the form `Sys.halting_dense_of_modCertN` takes. -/
theorem bigfoot_cert72 : ∀ u < 216, ∃ c : ℕ, c ≤ 2 ∧
    ((5 : ℕ) : ℤ) * bigfootSys.w.getD (u % bigfootSys.q) 0 +
      (bigfootφ72.getD (((bigfootSys.img u + (c : ℤ)) % ((72 : ℕ) : ℤ)).toNat) 0 : ℤ) + 1 ≤
        bigfootφ72.getD (u % 72) 0 := by
  decide +kernel

/-- **T3 stretch (Bigfoot, defect 2).**  Some member of `F_{L,2}` agreeing with the cryptid on
every block `< K` halts from `(10, 2)`.  Improves `bigfoot_halting_member` from defect `7`. -/
theorem bigfoot_halting_member_two {L : ℕ} (hL : 1 ≤ L) (K : ℤ) :
    ∃ σ : ℤ → Fin 3, (∀ b < K, σ b = 0) ∧ bigfootSys.Halts (member 24 L σ) (10, 2) :=
  bigfootSys.halting_dense_of_modCertN (Q := 72) (N := 216) (by decide) (by decide) hL
    (by decide) (by decide) (by decide) (by decide) (fun r => bigfootφ72.getD r 0) 5
    bigfoot_cert72 (fun x => bigfootE (bigfootSys.res x) = true) (fun _ => 0) K (10, 2)
    (bigfoot_E_orbit L) (fun x hx hE => bigfoot_esc x hx hE)

end Collatz.HydraFoils
