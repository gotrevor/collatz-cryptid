import Mathlib.Tactic

/-!
# The Syracuse map and parity vectors

For odd `n`, the Syracuse step is
  σ(n) = (3n + 1) / 2^{v₂(3n+1)}
i.e., perform one `3n+1` and then strip all factors of 2.

Equivalently, working only on odd values: `σ` is the "next odd" in the
classical Collatz orbit.  The **parity vector** records, for each Syracuse
step, the 2-adic valuation `v₂(3n+1)` (= how many halvings were stripped).

These are the natural ingredients for the 3-adic story behind Collatz,
and the natural counterpart to the base-3 digits of `2^n` we use in
`Erdos/Conjecture.lean`.
-/

namespace Collatz.Erdos

/-- Strip all factors of 2 from a positive natural.  `stripTwos 0 = 0`. -/
def stripTwos (m : ℕ) : ℕ :=
  if h : 0 < m ∧ m % 2 = 0 then
    have : m / 2 < m := Nat.div_lt_self h.1 (by decide)
    stripTwos (m / 2)
  else m
termination_by m

/-- Count the factors of 2 in `m`.  `twosCount 0 = 0`. -/
def twosCount (m : ℕ) : ℕ :=
  if h : 0 < m ∧ m % 2 = 0 then
    have : m / 2 < m := Nat.div_lt_self h.1 (by decide)
    1 + twosCount (m / 2)
  else 0
termination_by m

/-- The Syracuse step on odd `n`:  `σ(n) = (3n+1) / 2^{v₂(3n+1)}`.

Defined on all naturals; the interesting input domain is the odd
positives, which `σ` maps to odd positives. -/
def syracuse (n : ℕ) : ℕ := stripTwos (3 * n + 1)

/-- The 2-adic exponent stripped at one Syracuse step: `v₂(3n+1)`. -/
def syracuseExp (n : ℕ) : ℕ := twosCount (3 * n + 1)

/-- The **Syracuse parity vector** of length `k` of `n`: the list of
2-adic exponents stripped at each of the first `k` Syracuse steps. -/
def syracuseParityVec : ℕ → ℕ → List ℕ
  | _, 0 => []
  | n, k + 1 => syracuseExp n :: syracuseParityVec (syracuse n) k

/-- Unfolding lemma for `stripTwos` on inputs where `0 < m ∧ m % 2 = 0`. -/
theorem stripTwos_step {m : ℕ} (h : 0 < m ∧ m % 2 = 0) :
    stripTwos m = stripTwos (m / 2) := by
  rw [stripTwos]; simp [h]

/-- Unfolding lemma for `stripTwos` on odd or zero inputs. -/
theorem stripTwos_stop {m : ℕ} (h : ¬ (0 < m ∧ m % 2 = 0)) :
    stripTwos m = m := by
  rw [stripTwos]; simp [h]

theorem twosCount_step {m : ℕ} (h : 0 < m ∧ m % 2 = 0) :
    twosCount m = 1 + twosCount (m / 2) := by
  rw [twosCount]; simp [h]

theorem twosCount_stop {m : ℕ} (h : ¬ (0 < m ∧ m % 2 = 0)) :
    twosCount m = 0 := by
  rw [twosCount]; simp [h]

/-- σ(1) = 1  (the trivial Syracuse fixed point). -/
theorem syracuse_one : syracuse 1 = 1 := by
  change stripTwos 4 = 1
  rw [stripTwos_step (by decide), show (4 / 2 : ℕ) = 2 from rfl,
      stripTwos_step (by decide), show (2 / 2 : ℕ) = 1 from rfl,
      stripTwos_stop (by decide)]

/-- v₂(3·1+1) = v₂(4) = 2. -/
theorem syracuseExp_one : syracuseExp 1 = 2 := by
  change twosCount 4 = 2
  rw [twosCount_step (by decide), show (4 / 2 : ℕ) = 2 from rfl,
      twosCount_step (by decide), show (2 / 2 : ℕ) = 1 from rfl,
      twosCount_stop (by decide)]

/-- Parity vector of `1` is all `2`s (`1` is the fixed point with exponent 2). -/
theorem syracuseParityVec_one (k : ℕ) :
    syracuseParityVec 1 k = List.replicate k 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [syracuseParityVec, syracuse_one, syracuseExp_one, ih, List.replicate_succ]

end Collatz.Erdos
