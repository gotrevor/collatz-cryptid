/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.HydraFoils.Cert218Data

/-! # #218 certificate, chunk group A: `chk` on `[0, 60000)` by `decide +kernel` -/

set_option Elab.async false

namespace Collatz.HydraFoils.Cert218

theorem chunk0 : allRange chk 0 10000 = true := by decide +kernel

theorem chunk1 : allRange chk 10000 10000 = true := by decide +kernel

theorem chunk2 : allRange chk 20000 10000 = true := by decide +kernel

theorem chunk3 : allRange chk 30000 10000 = true := by decide +kernel

theorem chunk4 : allRange chk 40000 10000 = true := by decide +kernel

theorem chunk5 : allRange chk 50000 10000 = true := by decide +kernel

end Collatz.HydraFoils.Cert218
