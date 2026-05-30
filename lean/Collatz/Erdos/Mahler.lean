import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Collatz.Conjecture
import Collatz.Erdos.Conjecture

/-!
# Mahler's 3/2 problem (1968) and the open-problem triple

A **Z-number** is a positive real `x` whose `× (3/2)`-orbit modulo 1
lives entirely in `[0, 1/2)`:

  for every `n ≥ 0`,    `{x · (3/2)^n} < 1/2`.

**Mahler (1968) conjectured: no Z-number exists.**  This is open.

Best known partial result: Flatto–Lagarias–Pollington (1995) show that
if a Z-number exists, the density of `n` with `{x · (3/2)^n} ∈ [0, 1/2)`
is bounded; specifically, the density of indices where the orbit drifts
into the "wrong" half-interval is non-trivially positive.  (Not
formalized here.)

## Place in the family

Mahler's 3/2 problem sits alongside Collatz and Erdős as the
**real-orbit cousin** in the family of open problems about the joint
multiplicative behavior of 2 and 3:

| problem  | shape                                | underlying fact        |
|----------|--------------------------------------|------------------------|
| Collatz  | iterate `×3, ÷2` on ℕ              | log₂ 3 ∉ ℚ            |
| Erdős    | digits of `2^n` in base 3           | log₂ 3 ∉ ℚ            |
| Mahler   | orbit of `x` under `× (3/2)` mod 1  | log₂ 3 ∉ ℚ            |

All three would be trivial (or vacuous) if 2 and 3 were multiplicatively
dependent.  None is known to imply (or be implied by) another.

The Collatz–Mahler kinship is concrete on the iterate side: the
Syracuse map `T(n) = (3n+1)/2` for odd `n` is exactly the integer
analogue of multiplying by `3/2` and adding `1/2`, so Collatz orbits
are arithmetic shadows of the `×(3/2)` orbits Mahler studies.  But no
*logical* implication is known.
-/

namespace Collatz.Erdos

open Collatz

/-- `x` is a **Z-number**: a positive real whose `×(3/2)`-orbit modulo 1
stays in the lower half-interval `[0, 1/2)` forever. -/
def IsZNumber (x : ℝ) : Prop :=
  0 < x ∧ ∀ n : ℕ, Int.fract (x * (3 / 2 : ℝ) ^ n) < 1 / 2

/-- **Mahler's 3/2 conjecture (1968)**: there are no Z-numbers. -/
def MahlerNoZNumber : Prop := ∀ x : ℝ, ¬ IsZNumber x

/-! ## The open-problem triple

All three problems are open in 2026.  Packaging them lets a future
unification carry the conjunction as a hypothesis. -/

/-- Conjunction of the three open conjectures of the
"`2`-and-`3`-multiplicative-independence" family. -/
def OpenTriple : Prop :=
  Conjecture ∧ ErdosConjecture ∧ MahlerNoZNumber

/-! ## Open implications between the three

We don't know of a proof of any implication.  Stated as `Prop`s for
future reference; resolving any would be a real unification result. -/

/-- Open: does Mahler's conjecture imply Collatz? -/
def MahlerImpliesCollatz : Prop := MahlerNoZNumber → Conjecture

/-- Open: does Collatz imply Mahler's conjecture? -/
def CollatzImpliesMahler : Prop := Conjecture → MahlerNoZNumber

/-- Open: does Mahler imply Erdős? -/
def MahlerImpliesErdos : Prop := MahlerNoZNumber → ErdosConjecture

/-- Open: does Erdős imply Mahler? -/
def ErdosImpliesMahler : Prop := ErdosConjecture → MahlerNoZNumber

/-! ## Sanity observation (informal)

`x = 1` is **not** a Z-number: the first iterate already sits on the
boundary.

  `n = 0`:  `{1 · 1}   = 0      < 0.5`  ✓
  `n = 1`:  `{1 · 1.5} = 0.5`,   not `< 0.5`  ✗

So `1` escapes the Z-number condition at step 1.  The conjecture says
*every* positive real eventually escapes — but no `x` is known to be a
counterexample and no proof exists that none can be. -/

end Collatz.Erdos
