import Collatz.OrbitMin
import Collatz.LogDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Korec 1994 - statement-only formalization

Ivan Korec, *A density estimate for the 3x + 1 problem* (Math. Slovaca
44 (1994), no. 1, 85-89). The strongest pre-Tao "almost all" result:

> For every `θ > log₂(3) / 2 ≈ 0.7925`, the set
> `{N ∈ ℕ⁺ : Colmin(N) < N^θ}` has natural density `1`.

Korec strengthened earlier bounds by Terras (1976), Everett (1977), and
Allouche (1979). The exponent `log₂(3)/2 = log_4(3)` is sharp under
Korec's method (a weighted counting argument on the binary
representations of trajectories) and stood as the best known constant
for 25 years until Tao 2019.

## What we formalize

We state Korec's result with respect to **logarithmic** density rather
than natural density. This is a slight strengthening of stating it: any
set of natural density `1` automatically has logarithmic density `1`,
since `log` is a smoother (slower) averaging procedure that respects
density-`0` complements. Tao's paper Theorem 1.3 (in `Tao.lean`)
likewise uses logarithmic density and is consistent with this
convention. See Tao 2019 §1 for the natural-vs-log discussion.

## Relationship to Tao 2019

Tao's theorem strictly supersedes Korec's: it allows the bound `f(N)`
to grow arbitrarily slowly (e.g., `log log log log N`), whereas Korec
requires `f(N) = N^θ` with `θ > log_4(3)`. The Tao proof is 49 pages of
probabilistic 3-adic analysis. The Korec proof is ~5 pages of
elementary density bookkeeping on Collatz iterates - genuinely
tractable to formalize in Lean. That is the reason Korec is interesting
*formally* even though Tao subsumes it *mathematically*.

The proof is left as `sorry` here. Proof skeleton: see comments below.
-/

namespace Collatz

open Filter Topology

/-- **Theorem (Korec 1994)**: For any real `θ > log₂(3) / 2`, the
Collatz orbit minimum `colMin N` is less than `N^θ` for almost all
positive integers `N`, in the sense of logarithmic density.

`log₂(3) / 2 = log_4(3) ≈ 0.7925`. This was the best known exponent
prior to Tao 2019 (which removes the polynomial-growth restriction on
the threshold function altogether). -/
theorem korec1994 (θ : ℝ) (hθ : Real.logb 2 3 / 2 < θ) :
    AlmostAllPos (fun N => 1 ≤ N → ((colMin N : ℝ) < (N : ℝ) ^ θ)) := by
  sorry

/-!
## Proof skeleton (for future work)

Korec's argument has three pieces. The natural Lean breakdown:

1. **Trajectory descent lemma**. For each `N`, define the *first
   descent time* `τ(N) := min { k : T^[k] N < N }`. The Collatz
   trajectory `N, T N, T² N, ...` decreases below `N` infinitely often
   for almost all `N`; this is the Terras 1976 stopping-time result
   (already partly in `Conditional.lean` as `τ_ge_log2`).

2. **Density counting**. For `θ > log_4(3)` fixed, count the integers
   `N ≤ x` such that `T^[k] N ≥ N^θ` *for all* `k ≤ τ(N)`. Korec shows
   this count is `o(x)` by a weighted sum over the `2^τ` possible
   "parity sequences" of even/odd steps in the first `τ` iterations.
   The constant `log_4(3)` arises from comparing `(3/4)^(τ/2)` to the
   `N^θ` threshold.

3. **Closing the bound**. By (1) every trajectory eventually descends
   below `N`, and by (2) the descent reaches `N^θ` for almost all `N`,
   so `colMin N ≤ T^[τ(N)] N < N^θ` for almost all `N`.

Suggested decomposition into Lean files:

* Extend `Conditional.lean` with `descent_time` and prove its
  almost-everywhere finiteness (Terras).
* New file `KorecCounting.lean`: weighted parity-sequence sum giving
  the density-0 conclusion on the exceptional set.
* `Korec.lean` (this file): glue the above into `korec1994`.

Mathlib-relevant facts likely to be needed:

* `Nat.totient`-style counting machinery (probably not directly).
* `Real.logb` basic facts (`Real.logb_pos`, `Real.logb_lt_logb_iff`).
* `Real.rpow_natCast`, `Real.rpow_lt_rpow_left_iff`.
* `Filter.Tendsto` / `Filter.atTop` lemmas for the density limit
  (already imported transitively via `LogDensity.lean`).
* Natural-density-to-log-density transfer: not yet in mathlib in this
  form; would be a clean side-contribution.

-/

end Collatz
