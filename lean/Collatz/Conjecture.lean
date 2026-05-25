import Collatz.Basic

/-!
# The Collatz conjecture (as a `Prop`)

We package the conjecture as a single `Prop`, so theorems that depend on it
can carry it as a hypothesis.

Note: this is the *slow* Collatz conjecture - one `T`-step per iteration.
The fast / Syracuse variant is equivalent but uses a different step count.
-/

namespace Collatz

/-- Every positive integer eventually reaches `1` under iteration of `T`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ k, T^[k] n = 1

end Collatz
