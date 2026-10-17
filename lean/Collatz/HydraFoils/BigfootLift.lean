/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.HydraFoils

/-!
# Bigfoot drains at defects 2 and 1: lookahead certificates

The residue-level certificate for Bigfoot needs defect `7` (`bigfoot_drift`), and no
residue-level certificate exists at `d ≤ 6` [computed].  But the image `32 ⌊X/24⌋ + h` mod
`24` depends on `⌊X/24⌋` only mod `3` (as `32 ≡ 0 (mod 8)`), so a steering that knows
`X mod 72` knows the next residue exactly, and the adversary only picks the base-3 digit after
it.  On `X mod 72` the energy game is won at defect `2`: a potential `φ ≤ 10` on `X mod 72`
with, at every `X mod 216`, a choice `c ≤ 2` along which `5 w + φ` falls by one.  The check is
over `216` residues (`X mod 216` fixes the image mod `72`: `72 ∣ 32 · 9`), by `decide +kernel`.
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
      (bigfootφ72.getD (((bigfootSys.img u + (c : ℤ)) % ((72 : ℕ) : ℤ)).toNat) 0 : ℤ) +
        1 ≤
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

/-! ## Defect 1: four digits of lookahead

On `X mod 1944 = 8 · 3^5` the energy game is won at defect `1`: a potential `φ ≤ 31` with, at
every `X mod 5832`, a choice `c ≤ 1` along which `8 w + φ` falls by one (mean walk `≤ -1/8` per
step).  `X mod 648` does not suffice for `m ≤ 10` [computed].  `φ` is packed `5` bits per
residue into `P1944`; found by `sim/hydra_foils/energy.js 32 24 … 1944 3 1 8` and re-checked in
Python on all `X mod 24 · 1944`.  Defect `0` is the cryptid itself, so this is the floor. -/

/-- The defect-1 potential on `X mod 1944`, packed `5` bits per residue. -/
def P1944 : ℕ :=
  [0x3c50672006186c673ce648a660b646,
    0x055286a448a16886648873d4869b280560b9392b3952b0b4ab8c18b5a52b0c42a4a40a086ca72a4a,
    0x6a1aa1a5aa03128b9008a82284bd087c4283a36805109a2169411691ddc9bd0494a1c93ccc292c02,
    0x18e8264102bba42529c23f0a6b94064324656826a3826632462396972849082a96b4a9c89a94c689,
    0x4c9214b08128b01859c149d810a5e106d2dc240d5ae6d5c46d494ad1074d051e2ab142691220d182,
    0xb3ae212da23504b4b80b4914b135ab4a10b0c52b048c47280448b4494dc49246422aa41388bb10ab,
    0x081eb3d5abbc50b5ad2b3ec21824015ae615f6c172141289e10456dea40d5878da4c2d4a08d886cd,
    0x0420a834ca081ea3a42ae150a9466a6614348863123a3ad5a37210312223055078a0276970784ce7,
    0x73d0741ae705a48b48e8419c832c687d5c841d280542f7240f515af2da8f6298f245cf029ab8080b,
    0x8824b528eb6b42b3962b0316991029081290a429d39c9489a9544618bc01286e17caa18252141de1,
    0x054e2c20029968264502b24624bee23552bb24eb3164b52c6b8398b5a2eb04941694e130ae17c101,
    0x489410ca810598873088519c8364286c5a8497280452cca52c6052c0b4acb2a0c6392c350264a406,
    0x3930683d66599661a52604042b2002902a26b5a2a4422132c223c4e788ce2812e0c52ead04e5152e,
    0x2d8248ac04099c434524b4a445ae4437888e10486bac875428aace85b6e82bd697a0e90820944d69,
    0xf1d694d5c9750a44bc04393a4acd64496840ad2405e28ab40871e08458284a0e8107880424284582,
    0x581220a842ac2a2135c22c4485a008486284b1a87aa081adc804d087ac0878ec8751085a4c840de8,
    0x02909d8809081c934949e34a94b98965c819400131e01456217b541389a1060e9a2c094a24954829,
    0x4a429487490412aaa14a2822a4b4aae91ea7aa0a6e5034a0033a70386e63831832a6c30712a524ca,
    0x7b2ca750ca5ad4a28e0a05965d2c05799a52b8c5851e52a125058294b809619c934949498c90c5a9,
    0x0292ca880c8832c8b98c6a82c616cc03d89a1cc9081290bce99ce0949d691b4616bc01082c174641,
    0xab1a1516812d842f8882719e23d4a28b022626a20c14b838ab0822b4a42b8a8cb5a6cb0c567590c7,
    0x50787a55a7499c70b6a70656682ca67a5e63ec269cd064afc61c12f925cf3012f0bcef9a6af6ad2f,
    0x1c02764407082a76a9c74a1070b9270344281402a0202431625402210aa204048808a8301681c528,
    0xab528411e82dc678480731de73d5e7839c74316707505b20053b7659d425934c54ab851492aa258a,
    0x20a4a538cac890a835ea4d4e14a8012968164521491410a9210592ab240a91aaa6c4aa6a52a497aa,
    0x045e88ada8405280c0e8db60844e085c4ab5a40b7054b141eb735cb3316b058a5a2c0541b45949e5,
    0x728a529a05028ae9080e0812e0d18e938ce5a92e16421aa4012a6a16e621a2621499a124989c2409,
    0x70a89644297b02949e690392a9a46a181aa2a42ad21ca7a6aa56541488a1627e1bcdc169ce113621,
    0x07186538266b206464264b9263062606964d2c24729641c944ada84235242cc287ac0868e0844de8,
    0x49ce80ce6803d3099c70b0250528d07b03059e70035b1e14710819122431b3db180931340217c801,
    0x08201466819a101511411e047e88076a207440c78a467426a70c911c20b138a11438d1bacf193611].foldl
    (fun a b => a * 2 ^ 320 + b) 0

/-- Lookup in `P1944`. -/
def bigfootφ1944 (r : ℕ) : ℕ := Nat.mod (Nat.shiftRight P1944 (5 * r)) 32

set_option maxRecDepth 100000 in
/-- The defect-1 certificate, in the form `Sys.halting_dense_of_modCertN` takes. -/
theorem bigfoot_cert1944 : ∀ u < 5832, ∃ c : ℕ, c ≤ 1 ∧
    ((8 : ℕ) : ℤ) * bigfootSys.w.getD (u % bigfootSys.q) 0 +
      (bigfootφ1944 (((bigfootSys.img u + (c : ℤ)) % ((1944 : ℕ) : ℤ)).toNat) : ℤ) + 1 ≤
        bigfootφ1944 (u % 1944) := by
  decide +kernel

/-- **T3 stretch (Bigfoot, defect 1).**  Some member of `F_{L,1}` agreeing with the cryptid on
every block `< K` halts from `(10, 2)`.  Defect `1` is the least defect with a nontrivial
family, so this is the end of the ladder `7 → 2 → 1` for Bigfoot in the `X` coordinate. -/
theorem bigfoot_halting_member_one {L : ℕ} (hL : 1 ≤ L) (K : ℤ) :
    ∃ σ : ℤ → Fin 2, (∀ b < K, σ b = 0) ∧ bigfootSys.Halts (member 24 L σ) (10, 2) :=
  bigfootSys.halting_dense_of_modCertN (Q := 1944) (N := 5832) (by decide) (by decide) hL
    (by decide) (by decide) (by decide) (by decide) bigfootφ1944 8
    bigfoot_cert1944 (fun x => bigfootE (bigfootSys.res x) = true) (fun _ => 0) K (10, 2)
    (bigfoot_E_orbit L) (fun x hx hE => bigfoot_esc x hx hE)

end Collatz.HydraFoils
