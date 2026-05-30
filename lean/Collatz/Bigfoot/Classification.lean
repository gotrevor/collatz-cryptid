import Mathlib.Tactic
import Collatz.Bigfoot.Dynamics
import Collatz.Bigfoot.V6Rule

/-!
# Bigfoot's halting as a multidimensional generalized Collatz problem

## The framing

The classical Collatz conjecture concerns iteration of
`f(n) = if n even then n/2 else 3n+1` from `n = 1`. Two structural
features:

* **Residue case analysis**: which branch of `f` you take is determined
  by `n mod 2`.
* **Affine update per branch**: each branch is `n ↦ aᵢ · n + bᵢ` for
  rationals `(aᵢ, bᵢ)` chosen so the image is an integer.

Conway (1972) generalized this to *Generalized Collatz functions*: maps
`f : ℤ → ℤ` defined piecewise on `mod d` residues with each piece
affine and integer-preserving. He showed that the question "starting
from `x`, does iteration of `f` reach a fixed point?" is **undecidable
in general** for an arbitrary Generalized Collatz `f` (encoding TM
halting). Specific instances — Collatz itself, Mahler's `3/2` problem,
the `5n+1` variant — are open conjectures within this family.

Ligocki's `(a, b, c)` reduction of Bigfoot (`Dynamics.lean`, mirroring
his 2023-10-16 blog post) is a **3-dimensional generalized Collatz
function**: there are exactly 6 cases, indexed by `b mod 6`, each
specifying an affine update on `(a, b, c) ∈ ℕ³`. One case (`a = 0`,
`b ≡ 2 mod 6`) is a halt branch. The Bigfoot halting question is
*exactly* "does the orbit of this 3D-GenCollatz function from the
initial state ever hit the halt branch?"

## Consequence

Bigfoot's open content is "an instance of the 3D-GenCollatz family
behaves a certain way." Conway's undecidability result says some
instances are unknowable. Whether Bigfoot is one of them — i.e.,
whether its halting reduces to a *known* arithmetic conjecture — is
itself open. What we *can* say is: Bigfoot inhabits the Collatz
family, and the cascade-doesn't-close phenomenon we observe in
`V6KPos.lean` (the strengthened-invariant attempt) is a structural
feature of generalized Collatz analysis, not specific to this machine.

## References

* Conway, "Unpredictable iterations," 1972. Proceedings of the Number
  Theory Conference, Boulder.
* Lagarias, "The 3x+1 problem and its generalizations," 1985 (American
  Mathematical Monthly).
* Aaronson, "The busy beaver frontier," 2020 (SIGACT News survey).
* Ligocki, "BB(3,3) is hard," 2023-10-16 blog post.

This file is a structural classification artifact, not a closure
attempt. It is sorry-free; the open content stays in `V6KPos.lean` and
`Reduction.lean`.
-/

namespace Collatz.Bigfoot

open Dyn

/-! ## The residue-affine rule table

`bigfootRule r q a c` is the update rule that fires when
`d.b mod 6 = r` and `d.b / 6 = q`, with `(d.a, d.c) = (a, c)`. There
are exactly 6 rules; the only halt case is `(r = 2, a = 0)`. -/

/-- Bigfoot's `(a, b, c)` dynamics as a residue-affine table. -/
def bigfootRule (r q a c : ℕ) : Option Dyn :=
  match r with
  | 0 => some ⟨a,     8 * q + c - 1, 2⟩  -- A(a, 6q,   c) → A(a,   8q + c - 1, 2)
  | 1 => some ⟨a + 1, 8 * q + c - 1, 3⟩  -- A(a, 6q+1, c) → A(a+1, 8q + c - 1, 3)
  | 2 =>
      if a = 0 then none
      else some ⟨a - 1, 8 * q + c + 3, 2⟩  -- A(a, 6q+2, c) → A(a-1, 8q + c + 3, 2)
  | 3 => some ⟨a,     8 * q + c + 1, 5⟩  -- A(a, 6q+3, c) → A(a,   8q + c + 1, 5)
  | 4 => some ⟨a + 1, 8 * q + c + 3, 2⟩  -- A(a, 6q+4, c) → A(a+1, 8q + c + 3, 2)
  | 5 => some ⟨a,     8 * q + c + 5, 3⟩  -- A(a, 6q+5, c) → A(a,   8q + c + 5, 3)
  | _ => none  -- unreachable: residues live in {0..5}

/-! ### The classification theorem

`Dyn.step` reduces exactly to the residue-affine table. This is the
formal statement of "Bigfoot is a 3-dimensional generalized Collatz
function." -/

/-- **Bigfoot is a 3-dimensional generalized Collatz function.**
`Dyn.step d` agrees with `bigfootRule (d.b mod 6) (d.b / 6) d.a d.c`.
The proof is six concrete `decide`s, one per residue class. -/
theorem Dyn.step_eq_bigfootRule (d : Dyn) :
    Dyn.step d = bigfootRule (d.b % 6) (d.b / 6) d.a d.c := by
  unfold Dyn.step bigfootRule
  have h6 : d.b % 6 < 6 := Nat.mod_lt _ (by decide)
  -- Case-split on `d.b % 6 ∈ {0..5}`.
  rcases hmod : d.b % 6 with _ | _ | _ | _ | _ | _ | _
  case _ => simp  -- r = 0
  case _ => simp  -- r = 1
  case _ =>       -- r = 2: halt-or-step split
      by_cases ha : d.a = 0
      · simp [ha]
      · simp [ha]
  case _ => simp  -- r = 3
  case _ => simp  -- r = 4
  case _ => simp  -- r = 5
  case _ k => omega  -- contradiction: d.b % 6 ≥ 6

/-! ## The halt branch isolated

A single line capturing where the halt fires in the abstract framing. -/

/-- The halt branch of the Bigfoot generalized-Collatz function: rule
`r = 2` with `a = 0` is the unique state that returns `none`. -/
theorem bigfootRule_halt_iff (r q a c : ℕ) :
    bigfootRule r q a c = none ↔ (r = 2 ∧ a = 0) ∨ 6 ≤ r := by
  unfold bigfootRule
  rcases r with _ | _ | _ | _ | _ | _ | r
  · simp           -- r = 0
  · simp           -- r = 1
  · by_cases ha : a = 0 <;> simp [ha]  -- r = 2
  · simp           -- r = 3
  · simp           -- r = 4
  · simp           -- r = 5
  · -- r = k + 6: catch-all branch returns none; RHS true via 6 ≤ k+6.
    simp only [true_iff]
    right; omega

/-- Concrete corollary: `Dyn.step d = none ↔ (d.b mod 6 = 2 ∧ d.a = 0)`.
This is the *only* way Bigfoot's reduction can halt. -/
theorem Dyn.step_eq_none_iff (d : Dyn) :
    Dyn.step d = none ↔ d.b % 6 = 2 ∧ d.a = 0 := by
  rw [step_eq_bigfootRule, bigfootRule_halt_iff]
  have : d.b % 6 < 6 := Nat.mod_lt _ (by decide)
  constructor
  · rintro (h | h)
    · exact h
    · omega
  · intro h; left; exact h

/-! ## The Bigfoot non-halt conjecture, in pure-arithmetic form

`Dyn.orbit` is the iteration of `Dyn.step` from `Dyn.init = ⟨2, 1, 2⟩`.
Bigfoot's non-halt (modulo the V6 ↔ TM correspondence in
`Reduction.lean`) is the assertion that no orbit step lands on a state
with `b mod 6 = 2 ∧ a = 0`. -/

/-- **The Bigfoot non-halt conjecture, as a pure ℕ-arithmetic
statement.** Equivalent (via `Dyn.step_eq_none_iff` and induction on
`n`) to `∀ n, Dyn.orbit n ≠ none`. No TM, no tape, no encoding —
just iteration of a residue-affine map on `ℕ³` from a fixed initial
point. -/
def BigfootHypothesisArith : Prop :=
  ∀ n : ℕ, ∀ s : Dyn,
    Dyn.orbit n = some s → ¬ (s.b % 6 = 2 ∧ s.a = 0)

/-- Equivalence: the arithmetic statement is the same as
"every orbit step is `some`." -/
theorem BigfootHypothesisArith_iff :
    BigfootHypothesisArith ↔ ∀ n, Dyn.orbit n ≠ none := by
  unfold BigfootHypothesisArith
  constructor
  · -- (∀ n s, orbit n = some s → ¬ halt(s)) → (∀ n, orbit n ≠ none)
    intro h n hn
    -- Suppose orbit n = none. Then there's a least n_min with this property.
    -- orbit n_min ≠ orbit 0 (which is some init), so n_min ≥ 1; write n_min = m + 1.
    -- Then orbit (m+1) = (orbit m).bind step = none.
    -- If orbit m = none, that contradicts minimality. So orbit m = some s_m,
    -- and step s_m = none, i.e., (s_m.b mod 6 = 2 ∧ s_m.a = 0). Apply h.
    induction n with
    | zero =>
        -- orbit 0 = some init ≠ none, direct contradiction.
        have : Dyn.orbit 0 = some Dyn.init := rfl
        rw [this] at hn
        exact absurd hn (by simp)
    | succ n ih =>
        -- orbit (n+1) = (orbit n).bind step
        have h_succ : Dyn.orbit (n + 1) = (Dyn.orbit n).bind Dyn.step := rfl
        rw [h_succ] at hn
        cases hon : Dyn.orbit n with
        | none =>
            -- orbit n = none. By IH, contradiction.
            exact ih hon
        | some s =>
            -- orbit n = some s. Then hn becomes step s = none. Apply h.
            rw [hon] at hn
            simp only [Option.bind_some] at hn
            have hhalt := (Dyn.step_eq_none_iff s).mp hn
            exact h n s hon hhalt
  · -- (∀ n, orbit n ≠ none) → (∀ n s, orbit n = some s → ¬ halt(s))
    intro h n s hns ⟨hr, ha⟩
    -- s satisfies the halt condition, so step s = none, so orbit (n+1) = none.
    have h_step : Dyn.step s = none := (Dyn.step_eq_none_iff s).mpr ⟨hr, ha⟩
    have h_succ : Dyn.orbit (n + 1) = (Dyn.orbit n).bind Dyn.step := rfl
    rw [hns] at h_succ
    simp only [Option.bind_some] at h_succ
    rw [h_step] at h_succ
    exact h (n + 1) h_succ

/-! ## Cross-reference

The V6 (k, a, b, pat) coordinate system in `V6Rule.lean` is a
transformed view of the same dynamics, obtained via the bijection
`φ : Shawn (a, b, c) ↦ V6 (a, 2b-1, 2c+1, P1)` (and its inverse on
invertible states). The transformation moves multiplicative `b`
growth (4/3 per step in Shawn coords) to additive `b` growth (Δb ≤ 12
in V6 coords) — making the residue case analysis happen on `a` rather
than `b mod 6`, but the underlying dynamical system class is the same:
a piecewise-affine recurrence on `ℕ³ × {P1, P2}` with a halt branch.

V6's `k_pos` conjecture (`V6KPos.lean`) is equivalent to Bigfoot's
non-halt under the correspondence — both are statements about the
orbit of this generalized-Collatz family from a fixed initial point.
The "no finite cascade closes" phenomenon, documented in
`V6KPos.lean`, is the classical Collatz-style obstruction: each local
bound generates a fresh obligation at a strictly larger state, with no
global terminator. Conway's undecidability theorem for generic
Generalized Collatz functions tells us this is *possible* in general;
whether Bigfoot's *specific* instance is decidable remains open.
-/

end Collatz.Bigfoot
