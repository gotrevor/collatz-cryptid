/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.HydraFoils.Cert218Data

/-! # #218 certificate, chunk group B: `chk` on `[60000, 120000)` by `decide +kernel` -/

set_option Elab.async false

namespace Collatz.HydraFoils.Cert218

theorem chunk6 : allRange chk 60000 10000 = true := by decide +kernel

theorem chunk7 : allRange chk 70000 10000 = true := by decide +kernel

theorem chunk8 : allRange chk 80000 10000 = true := by decide +kernel

theorem chunk9 : allRange chk 90000 10000 = true := by decide +kernel

theorem chunk10 : allRange chk 100000 10000 = true := by decide +kernel

theorem chunk11 : allRange chk 110000 10000 = true := by decide +kernel

end Collatz.HydraFoils.Cert218
