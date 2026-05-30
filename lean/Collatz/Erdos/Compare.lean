import Collatz.Erdos.Basic
import Collatz.Erdos.Conjecture
import Collatz.Erdos.DoublingCA
import Collatz.Erdos.Syracuse

/-!
# Side-by-side comparison: Syracuse parity vector vs. base-3 digits of `2^n`

For each `n`, we have two natural sequences indexed by a "depth" `k`:

* `G(n, k) := 2^n mod 3^k`  — the first `k` base-3 digits of `2^n`,
  packed back into a number.  Erdős's conjecture is about whether
  these digits contain a `2`.

* `F(n, k) := syracuseParityVec n k`  — the first `k` 2-adic exponents
  stripped along the Syracuse orbit of `n`.  In the **slow** Collatz
  setting, parity vectors of length `k` are determined by `n mod 2^k`
  (Terras 1976); the Syracuse / 3-adic analogue is more subtle.

This file gives `#eval` dumps for small `n, k`.  We also state
`Prop`-level "candidate relationships" without proving any of them.

## What we are explicitly **not** claiming

We are *not* claiming a published equivalence between the Syracuse
parity vector and the base-3 digits of `2^n`.  Both are 3-adic objects
in different senses, and our purpose here is empirical:

  *Stare at the table, see if a pattern jumps out.*
-/

namespace Collatz.Erdos

/-- Map a parity vector (list of 2-adic exponents) into a natural number
via base-2 positional notation.  This is one of several reasonable
embeddings; we provide it so a parity vector can be compared numerically
to `2^n mod 3^k`. -/
def parityVecToNat (v : List ℕ) : ℕ := Nat.ofDigits 2 v

/-- Convenience: the first `k` base-3 digits of `2^n` as a list (length `≤ k`). -/
def lowDigits (n k : ℕ) : List ℕ := (Nat.digits 3 (2 ^ n)).take k

/-- `G(n, k) := 2^n mod 3^k`, the "first k digits" reading. -/
def G (n k : ℕ) : ℕ := 2 ^ n % 3 ^ k

/-- `F(n, k)` packaged as a list (the raw Syracuse parity vector). -/
def F (n k : ℕ) : List ℕ := syracuseParityVec n k

/-! ## Open relational questions, as `Prop`s.  No proofs claimed. -/

/-- Does the Syracuse parity vector of `2n+1` (any odd) and the base-3
expansion of `2^n` admit a finite-state translation? -/
def ParityVecBaseThreeFiniteState : Prop :=
  ∃ (S : Type) (_ : Fintype S) (δ : S → ℕ → S × ℕ) (s₀ : S),
    ∀ n : ℕ, ∀ k : ℕ,
      (List.foldl (fun (p : S × List ℕ) (e : ℕ) =>
                     let (s, acc) := p
                     let (s', d) := δ s e
                     (s', acc ++ [d]))
                  (s₀, []) (F (2 * n + 1) k)).2
      = lowDigits n k

/-- The Erdős "no-2" set and the Syracuse-fixed-point ancestors: do they
intersect non-trivially?  (Trivially they both contain `n = 0`.) -/
def NoTwoMeetsSyracuseAncestors : Prop :=
  ∀ n : ℕ, 8 < n → NoTwoInBase3 (2 ^ n) →
    ∃ m, syracuse m = 1 ∧ 2 * n + 1 = m

/-! ## Empirical dump. -/

/-- Tuple for one row: `(n, F(n,k), G(n,k), digits_3(2^n))`. -/
def compareRow (n k : ℕ) : ℕ × List ℕ × ℕ × List ℕ :=
  (n, F n k, G n k, Nat.digits 3 (2 ^ n))

/-- Compare on odd `n ∈ {1, 3, 5, 7, 9, 11, 13, 15}` with `k = 6`. -/
def compareOdds : List (ℕ × List ℕ × ℕ × List ℕ) :=
  [1, 3, 5, 7, 9, 11, 13, 15].map (compareRow · 6)

/-- Compare on even `n ∈ {0, 2, 4, 6, 8, 10, 12, 14}` (the Erdős-hard side)
  with `k = 6`. -/
def compareEvens : List (ℕ × List ℕ × ℕ × List ℕ) :=
  [0, 2, 4, 6, 8, 10, 12, 14].map (compareRow · 6)

/-- The known Erdős "no-2" exceptions, with their Syracuse data.  These
  three rows are where any direct equivalence would have to be visible. -/
def compareExceptions : List (ℕ × List ℕ × ℕ × List ℕ) :=
  [0, 2, 8].map (compareRow · 8)

#eval compareOdds
#eval compareEvens
#eval compareExceptions

end Collatz.Erdos
