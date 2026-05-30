import Collatz.Erdos.Basic
import Collatz.Erdos.Conjecture
import Collatz.Erdos.Partial
import Collatz.Erdos.CollatzLink
import Collatz.Erdos.DoublingCA
import Collatz.Erdos.Syracuse
import Collatz.Erdos.Lagarias
import Collatz.Erdos.CarrySplit
import Collatz.Erdos.Mahler
import Collatz.Erdos.Axioms
import Collatz.Erdos.SumsOfPowers
import Collatz.Erdos.Search
import Collatz.Erdos.Compare
import Collatz.Erdos.SUnit
import Collatz.Erdos.Cycle
import Collatz.Erdos.Lifting
import Collatz.Erdos.Equidistribution
import Collatz.Erdos.Carry
import Collatz.Erdos.CarryProcess
import Collatz.Erdos.Effectivity
import Collatz.Erdos.Sturmian

/-!
# Erdős's conjecture on base-3 digits of `2^n`, and its (open) relationship to Collatz

Entry point for the `Erdos/` subdirectory.  This module is intentionally
**not** imported from the root `Collatz.lean` — build it directly with

```
cd lean && lake build Collatz.Erdos
```

so we don't conflict with the parallel Busy-Beaver / Bigfoot work in the
`Collatz/Bigfoot/`, `Collatz/BB/`, and `Collatz/FatCoyote/` subdirectories.
-/
