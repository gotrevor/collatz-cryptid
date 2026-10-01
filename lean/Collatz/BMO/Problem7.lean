/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Beaver Math Olympiad problem 7: every term is odd

BMO#7 is the mathematical reformulation of the non-halting of the 6-state Turing machine
`1RB1RF_1RC0RA_1LD1RC_1LE0LE_0RA0LD_0RB---` from the all-0 tape.

Let `f n = n + 1 + (v₂(n+1) mod 2)`, `a 0 = 1` and `a (n+1) = f^[n+2] (a n / 2)`.
Does some `a k` turn out even?  No.

## The mechanism

`f n` is `n + 2` when `v₂(n+1)` is odd and `n + 1` otherwise.  So `f` climbs one step at a time
and skips the integers with odd 2-adic valuation.  Put `b n = a n - 1`.  Call `k` *higheven*
when `v₂ k ≥ 4` and `v₂ k` is even.  For `n ≥ 3`, the terms `b n` list, in increasing order, the
`k` with `v₂ k = 1`, or `k` higheven, or `k > 4` with `k - 4` higheven.  All of these are even.

*References:*

- [Beaver Math Olympiad wiki page](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) (§7)
- The ansatz is due to bbchallenge contributor planet246 (2025-09-30).  The proof by induction
  from it is by pomme_de_terre (2025-10-24), posted in the bbchallenge Discord:
  <https://discord.com/channels/960643023006490684/1421782442213376000/1431483206208852001>
-/

namespace Collatz.BMO.Problem7

/-! ## Sanity anchors -/

/-- The step function, as an executable definition. -/
def f (n : ℕ) : ℕ := n + 1 + padicValNat 2 (n + 1) % 2

/-- The BMO#7 sequence, as an executable definition. -/
def seq : ℕ → ℕ
  | 0 => 1
  | n + 1 => f^[n + 2] (seq n / 2)

/-- The first terms match the machine's orbit as posted by mxdys (2025-09-28):
`(0,1) → (1,3) → (2,5) → (3,7) → (4,11) → (5,15) → …`. -/
example : (List.range 6).map seq = [1, 3, 5, 7, 11, 15] := by decide +kernel

/-! ## The headline

Statement in the style of `google-deepmind/formal-conjectures`
`FormalConjectures/Other/BeaverMathOlympiad.lean`, so it can anchor a `formal_proof` link. -/

theorem beaver_math_olympiad_problem_7
    (f : ℕ → ℕ) (hf : f = fun n ↦ n + 1 + padicValNat 2 (n + 1) % 2)
    (a : ℕ → ℕ)
    (a_ini : a 0 = 1)
    (a_rec : ∀ n, a (n + 1) = f^[n + 2] (a n / 2)) :
    ¬ ∃ k, Even (a k) := by
  sorry

end Collatz.BMO.Problem7
