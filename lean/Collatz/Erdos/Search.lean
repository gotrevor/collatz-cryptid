import Collatz.Erdos.Basic
import Collatz.Erdos.Conjecture
import Collatz.Erdos.Lagarias

/-!
# Computable Erdős-witness search via Lagarias

For each odd `m`, walk the Syracuse trajectory until it reaches `1`
(within a step budget), record the total halvings `σ_k(m)`, and check
whether `2^{σ_k(m)}` has a `2` in its base-3 expansion.

A pair `(m, σ_k(m))` with `2 ∉ digits_3(2^{σ_k(m)})` corresponds to an
Erdős exception (currently known: `(1, 2)` and `(85, 8)`).

Finding a third such pair with `σ_k(m) > 8` would refute Erdős's
conjecture — by `4 · 10^16` of brute-force search, none has been found.
This is a Lean-side scaffold for the same search.
-/

namespace Collatz.Erdos

/-- Walk Syracuse for up to `fuel` steps starting at `n`, accumulating
the total halvings.  Returns `some (k, σ_k)` if the trajectory reaches
`1` within `fuel` steps; `none` otherwise. -/
def syracuseToOne : ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | _, _, _, 0 => none
  | n, acc, k, fuel + 1 =>
    if n = 1 then some (k, acc)
    else syracuseToOne (syracuse n) (acc + syracuseExp n) (k + 1) fuel

/-- Check whether `n` has the digit `2` in its base-3 expansion. -/
def hasTwoInBase3 (n : ℕ) : Bool := 2 ∈ Nat.digits 3 n

/-- For a single odd `m`, compute its Lagarias witness data:
`(m, k, σ_k(m), hasTwo(2^{σ_k(m)}))`.  Returns `none` if Syracuse hasn't
reached `1` within `fuel` steps. -/
def erdosCheck (m fuel : ℕ) : Option (ℕ × ℕ × ℕ × Bool) :=
  (syracuseToOne m 0 0 fuel).map (fun (k, sigma) =>
    (m, k, sigma, hasTwoInBase3 (2 ^ sigma)))

/-- Enumerate `erdosCheck` over odd `m ∈ [1, mMax)`.
A row with the last component `false` is an Erdős witness (no `2` in
`digits_3(2^σ)`); we expect exactly two such rows: `(1, 1, 2, false)`
and `(85, 1, 8, false)`. -/
def erdosSearch (mMax fuel : ℕ) : List (ℕ × ℕ × ℕ × Bool) :=
  ((List.range mMax).filter (· % 2 = 1)).filterMap (erdosCheck · fuel)

/-- Just the Erdős witnesses (Syracuse trajectories whose total halvings
`σ_k` give a power of 2 with no `2` in base 3). -/
def erdosWitnesses (mMax fuel : ℕ) : List (ℕ × ℕ × ℕ × Bool) :=
  (erdosSearch mMax fuel).filter (fun row => !row.2.2.2)

/-- Enumerate **every** prefix of the Syracuse trajectory: for each odd
`m`, return the list `[(k, σ_k(m)) : k = 0, 1, …, kMax]`.  Unlike
`syracuseToOne`, this does *not* stop when `n` reaches `1`, so we get
Lagarias decompositions at every step (including the "extra laps"
through the Syracuse fixed point `1 → 1`). -/
def syracusePrefixes (m kMax : ℕ) : List (ℕ × ℕ) :=
  let rec aux (n acc k : ℕ) (steps : ℕ) : List (ℕ × ℕ) :=
    match steps with
    | 0 => [(k, acc)]
    | s + 1 => (k, acc) :: aux (syracuse n) (acc + syracuseExp n) (k + 1) s
  aux m 0 0 kMax

/-- All `(m, k, σ_k(m))` witnesses for odd `m ∈ [1, mMax)` and `k ≤ kMax`
where `2^{σ_k(m)}` has no `2` in base 3.  This captures both Erdős
exceptions (`N = 2` and `N = 8`) and re-visits via the fixed point. -/
def erdosWitnessesAll (mMax kMax : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((List.range mMax).filter (· % 2 = 1)).flatMap (fun m =>
    (syracusePrefixes m kMax).filterMap (fun (k, sigma) =>
      if !(hasTwoInBase3 (2 ^ sigma)) then some (m, k, sigma) else none))

/-- The unique set of "exceptional σ values" surfaced by the search:
`σ` such that some odd `m ∈ [1, mMax)` reaches a Syracuse-prefix state
in `≤ kMax` steps with cumulative halvings `σ`, and `2^σ` has no `2`
in base 3.  Erdős's conjecture predicts this set is exactly `{0, 2, 8}`
for all `mMax, kMax`. -/
def exceptionalSigmas (mMax kMax : ℕ) : List ℕ :=
  let xs := (erdosWitnessesAll mMax kMax).map (fun (_, _, s) => s)
  xs.toArray.qsort (· < ·) |>.toList.dedup

-- **The empirical Erdős check**:
-- Every σ surfaced by the search lies in `{0, 2, 8}`.
-- (σ = 0 is the trivial `k = 0` row for every m; the real exceptions are 2 and 8.)
#eval exceptionalSigmas 100 6
#eval exceptionalSigmas 300 10
#eval exceptionalSigmas 1000 12

-- Stress: how far can Lean's #eval push the search?
#eval exceptionalSigmas 5000 18
#eval exceptionalSigmas 20000 22

end Collatz.Erdos
