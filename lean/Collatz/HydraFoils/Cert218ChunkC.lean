/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.HydraFoils.Cert218Data

/-! # #218 certificate, chunk group C: `chk` on `[120000, 177147)` by `decide +kernel` -/

set_option Elab.async false

namespace Collatz.HydraFoils.Cert218

theorem chunk12 : allRange chk 120000 10000 = true := by decide +kernel

theorem chunk13 : allRange chk 130000 10000 = true := by decide +kernel

theorem chunk14 : allRange chk 140000 10000 = true := by decide +kernel

theorem chunk15 : allRange chk 150000 10000 = true := by decide +kernel

theorem chunk16 : allRange chk 160000 10000 = true := by decide +kernel

theorem chunk17 : allRange chk 170000 7147 = true := by decide +kernel

end Collatz.HydraFoils.Cert218
