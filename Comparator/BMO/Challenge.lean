/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Beaver Math Olympiad - comparator CHALLENGE (the trusted audit surface)

This file imports only Mathlib.  `Solution.lean` must prove these exact statements.
`comparator` checks that each one is identical in the solution.  It replays the proofs through
the Lean kernel and `nanoda`, and allows only `propext`, `Quot.sound` and `Classical.choice`.

* BMO#3 and BMO#4 are copied byte-for-byte from `google-deepmind/formal-conjectures`
  `FormalConjectures/Other/BeaverMathOlympiad.lean` at `137aec5c`.
* BMO#7 is not in formal-conjectures yet.  It is transcribed from the
  [BMO wiki](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) §7, in the same style.
-/

namespace Collatz.BMO.Problem3

theorem beaver_math_olympiad_problem_3
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n + 1) = (a n) + 2 ^ ((padicValNat 2 (a n)) + 2) - 1) :
    ¬ (∃ n k, a n = 4 ^ k) := by
  sorry

end Collatz.BMO.Problem3

namespace Collatz.BMO.Problem4

theorem beaver_math_olympiad_problem_4
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n+1)
      = if a n % 3 = 0 then a n / 3 + 2 ^ n + 1 else (a n - 2) / 3 + 2 ^ n - 1) :
    ¬ (∃ n, a n % 3 = 1) := by
  sorry

end Collatz.BMO.Problem4

namespace Collatz.BMO.Problem7

theorem beaver_math_olympiad_problem_7
    (f : ℕ → ℕ) (hf : f = fun n ↦ n + 1 + padicValNat 2 (n + 1) % 2)
    (a : ℕ → ℕ)
    (a_ini : a 0 = 1)
    (a_rec : ∀ n, a (n + 1) = f^[n + 2] (a n / 2)) :
    ¬ ∃ k, Even (a k) := by
  sorry

end Collatz.BMO.Problem7
