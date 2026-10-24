/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.GoodsteinTM.Sim

/-!
# Every Goodstein machine halts

Headline: the machine for any well-formed seed tree halts.  `halt_4.json` and `halt_16.json` are the
instances for `[1, 2, 3]` and `[1, 2, 3, 4]`.  The route is in `GOODSTEIN-TM-NEXT.md`.
-/

namespace GoodsteinTM

theorem halts_of_wf (t : List ℕ) (ht : WF t) : Halts (machine (cellsOf t)) start := by
  exact halts_of_wf_sim t ht

theorem halt_four_halts : Halts (machine (cellsOf [1, 2, 3])) start :=
  halts_of_wf _ (by decide)

theorem halt_sixteen_halts : Halts (machine (cellsOf [1, 2, 3, 4])) start :=
  halts_of_wf _ (by decide)

end GoodsteinTM
