import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed

/-!
# Logarithmic density

Tao 2019 uses *logarithmic density* to define "almost all" Collatz
orbits. Definition (his Def. 1.2):

For finite non-empty `R ⊂ ℕ+`, the logarithmically uniform
distribution `Log(R)` on `R` is

```
P(Log(R) ∈ A) = (Σ_{N ∈ A ∩ R} 1/N) / (Σ_{N ∈ R} 1/N)
```

The logarithmic density of `A ⊂ ℕ+` is

```
logDensity(A) := lim_{x→∞} P(Log(ℕ+ ∩ [1, x]) ∈ A)
                = lim_{x→∞} (Σ_{1 ≤ N ≤ x, N ∈ A} 1/N) / (Σ_{1 ≤ N ≤ x} 1/N)
```

provided the limit exists. We say a property `P` holds for *almost all*
`N ∈ ℕ+` if `{N | P N}` has logarithmic density `1`.

This file gives the precise formal definitions. No proofs about
properties of `logDensity` here - just the definitions plus statement-
level wiring for `Tao.lean`.
-/

namespace Collatz

open Filter Topology

-- The finite-set log-uniform "score": Σ_{N ∈ A ∩ R} 1/N for the
-- fragment of A lying in finite R ⊂ ℕ+.
open Classical in
noncomputable def logSum (A : Set ℕ) (R : Finset ℕ) : ℝ :=
  ∑ N ∈ R.filter (· ∈ A), (1 : ℝ) / N

/-- Probability mass of `A` under `Log(R)`. -/
noncomputable def logProb (A : Set ℕ) (R : Finset ℕ) : ℝ :=
  logSum A R / logSum Set.univ R

/-- The "window" `ℕ+ ∩ [1, x]` as a `Finset`. -/
noncomputable def posInterval (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (· ≥ 1)

/-- Logarithmic density of `A ⊂ ℕ+`, defined as the limit (if it
exists) of `logProb A (posInterval x)` as `x → ∞`. We use the predicate
form so the definition makes sense even when the limit may not exist;
to assert a specific value `d`, use `HasLogDensity A d`. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun x => logProb A (posInterval x)) atTop (𝓝 d)

/-- A property `P` holds for *almost all* `N ∈ ℕ+` in the sense of
logarithmic density if the set `{N | P N}` has log density `1`. -/
def AlmostAllPos (P : ℕ → Prop) : Prop :=
  HasLogDensity {N | P N} 1

end Collatz
