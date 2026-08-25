import Collatz.OrbitMin
import Collatz.LogDensity

/-!
# Tao 2019 - statement-only formalization

Terence Tao, *Almost all orbits of the Collatz map attain almost
bounded values* (arXiv:1909.03562, v5 2022). Theorem 1.3:

> Let `f : ℕ+ → ℝ` be any function with `lim_{N→∞} f(N) = +∞`.
> Then `Colmin(N) < f(N)` for almost all `N ∈ ℕ+` (in the sense of
> logarithmic density).

In Lean, with our definitions from `OrbitMin.lean` (`colMin`) and
`LogDensity.lean` (`AlmostAllPos`):

The Collatz orbit minimum `colMin N` is the infimum of
`{T^[k] N : k ∈ ℕ}` (matches Tao's `Colmin`).

"Almost all" means logarithmic density 1, i.e., the property holds on
a subset of `ℕ+` with `HasLogDensity ... 1`.

The theorem is stated below; proof left as `sorry`. The substance of
Tao's paper is the proof - 49 pages of probability theory on 3-adic
cyclic groups, characteristic function estimates, and a 2D renewal
process. We don't attempt that here.
-/

namespace Collatz

open Filter Topology

/-- **Theorem 1.3 (Tao 2019)**: For any function `f : ℕ → ℝ` with
`f(N) → ∞` as `N → ∞`, the Collatz orbit minimum `colMin N` is less
than `f(N)` for almost all positive integers `N` (in the sense of
logarithmic density).

This is the strongest known "almost all" result on Collatz. It
supersedes the natural-density results of Terras, Everett, Allouche,
and Korec (which gave `colMin N < N^θ` for `θ > log₂(3)/2 ≈ 0.79`),
allowing `f` to grow arbitrarily slowly (e.g., `f(N) = log log log log N`).

The proof is *not* attempted here. See [arXiv:1909.03562](https://arxiv.org/abs/1909.03562). -/
theorem tao2019 (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    AlmostAllPos (fun N => 1 ≤ N → ((colMin N : ℝ) < f N)) := by
  sorry

end Collatz
