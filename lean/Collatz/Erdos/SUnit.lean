import Mathlib.Tactic
import Collatz.Erdos.Conjecture
import Collatz.Erdos.Axioms
import Collatz.Erdos.SumsOfPowers

/-!
# The {2,3}-S-unit family and a shared effectivity frontier

Four ostensibly different open problems are instances of one equation family
`∑ cᵢ · 2^{aᵢ} · 3^{bᵢ} = 0` with fixed small coefficients `cᵢ`:

| family             | equation                                   | #terms  |
|--------------------|--------------------------------------------|---------|
| **Erdős-k**        | `2^N = 3^{a₁}+…+3^{a_k}` (distinct)         | `k+1`   |
| **Collatz n-cycle**| `x·(2^L−3^n) = R(e)` (Lagarias)             | `n+2`   |
| **symmetric (r,s)**| `2^{a₁}+…+2^{a_r} = 3^{b₁}+…+3^{b_s}`        | `r+s`   |
| **Pillai-c**       | `2^x − 3^y = c`                             | `3`     |

The **number of monomial terms** governs difficulty:

* `≤ 3` terms — Baker's theorem on linear forms in two logarithms bounds
  solutions *effectively*.
* `4` terms — the textbook ineffectivity wall (Evertse / Schlickewei–Schmidt
  subspace theorem gives finiteness but no computable bound).  In practice many
  4-term cases are still dispatched by *elementary* congruence/valuation
  arguments (e.g. Erdős `k=3` has **no** solutions, killed mod 8 — see
  `SumsOfPowers.two_pow_ne_three_term_three_pow_sum`).
* `5` terms — the smallest term count where a {2,3}-S-unit family exhibits a
  *sporadic* solution that elementary methods don't dispatch (Erdős `N=8`;
  symmetric `2²+2⁴+2⁶ = 3¹+3⁴`).

⚠️ **CRITIQUE (Trevor, 2026-05-28) — the "m=5 frontier" largely strips the easy
cases.** Two corrections kill the original "resolve 5-term ⟹ resolve all" claim:

1. **The difficulty is asymptotic, not at the smallest open case.** A large
   Erdős counterexample `2^n` (`n > 8`) has `~ n·log₃2 ≈ 0.63n` ternary digits,
   so it lives at term count `k ~ 0.63n` — *growing with n*, not `k=4`.  A
   nontrivial Collatz cycle has `n` in the billions (Eliahou), so it lives at
   huge term count, not the `3`-cycle.  Resolving `m=5` touches only the
   smallest sporadic shell; the real content is uniform-in-parameter (the
   exceptional/outlier set), exactly the density-1-easy / measure-0-hard
   structure of Tao 2019 for Collatz.

2. **`m=5` is not even special for provability.** Finiteness at *fixed* `k`
   (including `k=4`) is already a theorem (subspace theorem, Evertse /
   Schlickewei–Schmidt) — just ineffective.  The ineffectivity wall is at
   `m=4` (≥3 unit summands) and is the *same wall at every* `m ≥ 4`.  There is
   no distinguished `5`.  The `4`-vs-`5` gap was only ever about which cases
   *elementary* tricks happen to clear — a patchwork, not a frontier.

**What survives**: (a) these problems really are {2,3}-S-unit / linear-forms-in-
logs instances (known: Lagarias, Eliahou); (b) they share the **abc umbrella**
for *effective* resolution (known).  The genuine coupling — if any is novel —
must live in the **outlier structure** (large-parameter regime), e.g. shared
continued-fraction structure of `log₂3`, not in small-case term counting.

This file keeps the *provable* structural facts (the family defs, the 5-term
*coincidence* as a true-but-shallow observation, reuse of the proved ≤3-term
Erdős cases) and records the critique so the KB doesn't carry the overclaim.

See `notes/23-mahler-sunit-frontier.md`.
-/

namespace Collatz.Erdos

/-! ## Term-count functions (the organizing invariant) -/

/-- Erdős `k`-term equation `2^N = ∑ 3^{aᵢ}` is an `(k+1)`-term S-unit equation. -/
def erdosTerms (k : ℕ) : ℕ := k + 1

/-- Collatz `n`-cycle (`x=1`): `2^L = 3^n + ∑_{j} 3^{n-j}2^{S_{j-1}}` has `n+2` terms. -/
def collatzCycleTerms (n : ℕ) : ℕ := n + 2

/-- Symmetric `(r,s)`: `∑ 2^{aᵢ} = ∑ 3^{bⱼ}` has `r+s` terms. -/
def symTerms (r s : ℕ) : ℕ := r + s

/-- Pillai `2^x − 3^y = c` is a `3`-term equation. -/
def pillaiTerms : ℕ := 3

/-- **The 5-term alignment.** The three famous open cases — Erdős `k=4`,
the Collatz `3`-cycle, and the symmetric `(3,2)` problem — are all `5`-term
{2,3}-S-unit equations.  This is the structural heart of the frontier
observation: they are not independently hard, they sit on one wall. -/
theorem five_term_alignment :
    erdosTerms 4 = 5 ∧ collatzCycleTerms 3 = 5 ∧ symTerms 3 2 = 5 := by
  decide

/-- The general correspondence `Erdős k ↔ Collatz (k−1)-cycle`: same term count.
For `k ≥ 1`, the Erdős `k`-term equation and the Collatz `(k−1)`-cycle equation
have equal term counts. -/
theorem erdos_collatz_termcount (k : ℕ) (hk : 1 ≤ k) :
    erdosTerms k = collatzCycleTerms (k - 1) := by
  unfold erdosTerms collatzCycleTerms; omega

/-! ## Solution sets (uniform `Set.Finite` idiom, matching `Axioms.PillaiConjecture`) -/

/-- Erdős `k`-term solution set: `(N, S)` with `S` a set of `k` distinct
exponents summing (as powers of 3) to `2^N`. -/
def ErdosSol (k : ℕ) : Set (ℕ × Finset ℕ) :=
  { p | p.2.card = k ∧ (2 : ℕ) ^ p.1 = ∑ a ∈ p.2, 3 ^ a }

/-- Symmetric `(r,s)` solution set. -/
def SymSol (r s : ℕ) : Set (Finset ℕ × Finset ℕ) :=
  { p | p.1.card = r ∧ p.2.card = s ∧ (∑ a ∈ p.1, (2 : ℕ) ^ a) = ∑ b ∈ p.2, 3 ^ b }

/-- Pillai solution set for fixed `c`. -/
def PillaiSol (c : ℤ) : Set (ℕ × ℕ) :=
  { p | (2 : ℤ) ^ p.1 - 3 ^ p.2 = c }

/-! ## Concrete witnesses (sporadic 5-term solutions; the frontier is non-vacuous) -/

/-- Erdős `N=8`: the famous `k=4` sporadic solution `2⁸ = 3⁵+3²+3+1`. -/
theorem witness_erdos_8 : (2 : ℕ) ^ 8 = 3 ^ 5 + 3 ^ 2 + 3 ^ 1 + 3 ^ 0 := by norm_num

/-- Symmetric `(3,2)` sporadic solution `2²+2⁴+2⁶ = 3¹+3⁴` (= 84), found in the
independent-family survey.  A 5-term solution with no elementary completeness proof. -/
theorem witness_sym_84 : (2 : ℕ) ^ 2 + 2 ^ 4 + 2 ^ 6 = 3 ^ 1 + 3 ^ 4 := by norm_num

/-- Another symmetric `(3,2)` sporadic solution `2²+2³+2⁴ = 3⁰+3³` (= 28). -/
theorem witness_sym_28 : (2 : ℕ) ^ 2 + 2 ^ 3 + 2 ^ 4 = 3 ^ 0 + 3 ^ 3 := by norm_num

/-- The `N=8` witness as membership in `ErdosSol 4`. -/
theorem witness_erdos_8_mem : ((8 : ℕ), ({0, 1, 2, 5} : Finset ℕ)) ∈ ErdosSol 4 := by
  refine ⟨by decide, ?_⟩
  decide

/-! ## Reuse of the proved ≤ 3-term Erdős cases (the effective side of the wall) -/

/-- `Erdős k=1` is exactly solved: `2^N = 3^a ↔ N = a = 0` (the `N=0` exception).
Re-exported from `SumsOfPowers`. -/
theorem erdos_k1_solved {a n : ℕ} (h : 2 ^ n = 3 ^ a) : n = 0 ∧ a = 0 :=
  two_pow_eq_one_term_three_pow h

/-- `Erdős k=2` is exactly solved via **Catalan**: unique solution `N=2`.
Re-exported from `Axioms`. -/
theorem erdos_k2_solved {a b n : ℕ} (hab : b < a) (h : 2 ^ n = 3 ^ a + 3 ^ b) :
    n = 2 ∧ a = 1 ∧ b = 0 :=
  two_pow_eq_two_term_three_pow_sum hab h

/-- `Erdős k=3` is exactly solved (elementary, mod 8): **no** solutions.
Re-exported from `SumsOfPowers`. This is a 4-term equation dispatched by an
elementary trick — illustrating why the *empirical* frontier is at 5, not 4. -/
theorem erdos_k3_solved {a b c n : ℕ} (h1 : c < b) (h2 : b < a) :
    2 ^ n ≠ 3 ^ a + 3 ^ b + 3 ^ c :=
  two_pow_ne_three_term_three_pow_sum h1 h2

/-! ## The master conjecture and the m=5 frontier -/

/-- **Effective {2,3}-S-unit conjecture** (master; implied by abc).
Every Erdős, symmetric, and Pillai family has a finite solution set.

Finiteness for `≤ 3`-term families (Pillai, Erdős `k≤2`) is a *theorem* (Baker).
Finiteness for `≥ 4`-term families follows from the subspace theorem but
*ineffectively*; abc would make it effective.  We package the whole family. -/
def EffectiveSUnit23 : Prop :=
  (∀ k, (ErdosSol k).Finite) ∧
  (∀ r s, (SymSol r s).Finite) ∧
  (∀ c : ℤ, (PillaiSol c).Finite)

/-- **abc is the common parent.** Conjecturally `abc ⟹` effective control of the
whole {2,3}-S-unit family.  This is the umbrella under which Erdős, Collatz
cycles, and Pillai all sit. (Stated, not proved — this *is* the open content.) -/
def AbcImpliesEffectiveSUnit : Prop := AbcConjecture → EffectiveSUnit23

/-- The **5-term coincidence** (true but shallow): the smallest sporadic case of
Erdős, the symmetric family, and the Collatz cycle problem all sit at term count
5.  Provable, but — per the critique above — this is *not* where the difficulty
lives, so it is recorded as an observation, not a frontier. -/
def FiveTermCoincidence : Prop :=
  EffectiveSUnit23 → ((ErdosSol 4).Finite ∧ (SymSol 3 2).Finite)

theorem five_term_coincidence : FiveTermCoincidence := by
  intro h; exact ⟨h.1 4, h.2.1 3 2⟩

/-- **Where the difficulty actually is** (the honest target).

A counterexample to Erdős at `n` has `~0.63·n` ternary digits, so the conjecture
is really a statement about *unboundedly* many terms.  The content is the
**uniform** claim — finiteness across *all* `k` simultaneously — which is exactly
what `EffectiveSUnit23` (and behind it, abc) supplies, and what no fixed-`k`
result reaches.  This is the {2,3}-analogue of Tao's density-1/measure-0 split
for Collatz: the typical case is easy, the exceptional set is the whole problem. -/
def AsymptoticContent : Prop := ∀ k, (ErdosSol k).Finite

/-- The full Erdős conjecture needs the asymptotic content, not any single `k`:
a single fixed-`k` finiteness (even `k=4`) cannot bound `n`, because large
counterexamples have large `k`.  We record this as the honest direction of
implication: the *uniform* statement is the load-bearing one. -/
theorem asymptotic_is_the_master :
    EffectiveSUnit23 → AsymptoticContent := fun h => h.1

end Collatz.Erdos
