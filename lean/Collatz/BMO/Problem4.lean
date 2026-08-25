import Mathlib

/-!
# Beaver Math Olympiad problem 4 — Bonnie never finishes

BMO#4 is the mathematical reformulation of the non-halting of the 2-state 5-symbol
Turing machine `1RB3RB---1LB0LA_2LA4RA3LA4RB1LB` from the all-0 tape.

Bonnie the beaver builds a sequence with `a 0 = 2` and

* `a (n+1) = a n / 3 + 2 ^ n + 1`       if `a n ≡ 0 (mod 3)`,
* `a (n+1) = (a n - 2) / 3 + 2 ^ n - 1` if `a n ≡ 2 (mod 3)`,

and plans to stop as soon as some term is `≡ 1 (mod 3)`.  She never stops.

## The mechanism

`a n` grows like `(3/5) · 2 ^ n`, and the error term is periodic with period 4 because
`2 ^ n` cycles mod 5.  Clearing the denominator gives a subtraction-free invariant that
is exactly linear in `2 ^ n`, so each induction step is pure linear arithmetic:

| `n % 4` | invariant                | forced residue |
|---------|--------------------------|----------------|
| `0`     | `5 * a n = 3 * 2 ^ n + 7`| `a n % 3 = 2`  |
| `1`     | `5 * a n + 6 = 3 * 2 ^ n`| `a n % 3 = 0`  |
| `2`     | `5 * a n = 3 * 2 ^ n + 3`| `a n % 3 = 0`  |
| `3`     | `5 * a n = 3 * 2 ^ n + 6`| `a n % 3 = 0`  |

The residue column is *forced* by the invariant (e.g. `5 * a n = 3 * 2 ^ n + 7` implies
`2 * a n ≡ 1 (mod 3)`), which is what resolves the `if` in the recurrence and makes the
step deterministic.  No case ever produces `a n % 3 = 1`, which is the headline.

*References:*

- [Beaver Math Olympiad wiki page](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad)
  (§4, where the closed form is stated and attributed to Daniel Yuan, July 2024)
- Statement as posed in
  [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean)
-/

namespace Collatz.BMO.Problem4

/-! ## Sanity anchors

A concrete witness for the recurrence, so the transcription above can be checked against
the ten terms printed on the wiki: `2, 0, 3, 6, 11, 18, 39, 78, 155, 306`. -/

/-- Bonnie's sequence, as an executable definition. -/
def bonnie : ℕ → ℕ
  | 0 => 2
  | n + 1 => if bonnie n % 3 = 0 then bonnie n / 3 + 2 ^ n + 1
             else (bonnie n - 2) / 3 + 2 ^ n - 1

/-- The first ten terms match the ones published on the BMO wiki page. -/
example : (List.range 10).map bonnie = [2, 0, 3, 6, 11, 18, 39, 78, 155, 306] := by
  decide

/-! ## The invariant -/

variable {a : ℕ → ℕ}

/-- The closed form of Bonnie's sequence, with the denominator cleared so that the
statement is subtraction-free and linear in `2 ^ n`.  All four branches are carried
simultaneously because the induction step advances `n % 4`. -/
theorem closed_form (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1)
      = if a n % 3 = 0 then a n / 3 + 2 ^ n + 1 else (a n - 2) / 3 + 2 ^ n - 1) (n : ℕ) :
    (n % 4 = 0 → 5 * a n = 3 * 2 ^ n + 7) ∧
    (n % 4 = 1 → 5 * a n + 6 = 3 * 2 ^ n) ∧
    (n % 4 = 2 → 5 * a n = 3 * 2 ^ n + 3) ∧
    (n % 4 = 3 → 5 * a n = 3 * 2 ^ n + 6) := by
  induction n with
  | zero => simp [a_ini]
  | succ n ih =>
    obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
    have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hrec := a_rec n
    -- `n % 4` is one of the four residues; each fixes the invariant at `n`, which in turn
    -- fixes `a n % 3`, which resolves the `if`.
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · have hinv := ih0 h
      rw [if_neg (by omega)] at hrec
      refine ⟨by omega, by omega, by omega, by omega⟩
    · have hinv := ih1 h
      rw [if_pos (by omega)] at hrec
      refine ⟨by omega, by omega, by omega, by omega⟩
    · have hinv := ih2 h
      rw [if_pos (by omega)] at hrec
      refine ⟨by omega, by omega, by omega, by omega⟩
    · have hinv := ih3 h
      rw [if_pos (by omega)] at hrec
      refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## The headline

Statement transcribed verbatim from `google-deepmind/formal-conjectures`,
`FormalConjectures/Other/BeaverMathOlympiad.lean`. -/

/-- **BMO#4.** Bonnie never writes a term that is `≡ 1 (mod 3)`, so she never finishes. -/
theorem beaver_math_olympiad_problem_4
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n+1)
      = if a n % 3 = 0 then a n / 3 + 2 ^ n + 1 else (a n - 2) / 3 + 2 ^ n - 1) :
    ¬ (∃ n, a n % 3 = 1) := by
  rintro ⟨n, hn⟩
  obtain ⟨h0, h1, h2, h3⟩ := closed_form a_ini a_rec n
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have := h0 h; omega
  · have := h1 h; omega
  · have := h2 h; omega
  · have := h3 h; omega

end Collatz.BMO.Problem4

-- Axiom audit (kept at the end of the file so it reports on the finished declarations).
#print axioms Collatz.BMO.Problem4.closed_form
#print axioms Collatz.BMO.Problem4.beaver_math_olympiad_problem_4
