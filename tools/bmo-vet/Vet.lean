/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Collatz.BMO.Problem7
import Collatz.BMO.Problem9

/-!
# BMO#7 and BMO#9 statement vetting: the Lean side

Run by `tools/sandbox/bmo_statement_vet.py`, which compares the printed trajectories with
independent Python implementations of the wiki's definitions.

Each `example` instantiates the proved headline with concrete data.  It typechecks only if the
data satisfies the headline's hypotheses *as stated*.  This gives two facts at once:

* the hypotheses are satisfiable, so the theorem is not vacuous;
* the recurrences below match the statement, so `#eval` on them evaluates the statement's own
  definitions, not a re-typed copy.
-/

namespace BMOVet

/-! ## BMO#7 -/

def f7 : ℕ → ℕ := fun n ↦ n + 1 + padicValNat 2 (n + 1) % 2

def a7 : ℕ → ℕ
  | 0 => 1
  | n + 1 => f7^[n + 2] (a7 n / 2)

example : ¬ ∃ k, Even (a7 k) :=
  Collatz.BMO.Problem7.beaver_math_olympiad_problem_7 f7 rfl a7 rfl fun _ ↦ rfl

/-! ## BMO#9 -/

/-- One step of BMO#9's recurrence, as a map on configurations. -/
def R (y : ℕ → ℕ) : ℕ → ℕ :=
  if y 0 = 0 then
    fun i ↦ if i = 0 then 3 + y 1 + y 2 else y (i + 2)
  else if y 0 = 1 then
    fun i ↦ if i = 0 then y 1 - 1 else if i = 1 then 0 else if i = 2 then 1
      else if i = 3 then 1 + y 2 else y (i - 1)
  else
    fun i ↦ if i = 0 then y 0 - 2 else if i ≤ 2 then 1 + y i else y i

example : ¬ ∃ n, R^[n] (fun _ ↦ 0) 0 = 1 ∧ R^[n] (fun _ ↦ 0) 1 = 0 :=
  BMO9.beaver_math_olympiad_problem_9 (fun n ↦ R^[n] fun _ ↦ 0) rfl
    fun n ↦ Function.iterate_succ_apply' R n _

/-- `R` on a finite-support configuration.  Index `i` of `R y` reads `y` at most at `i + 2`,
and the support grows by at most one per step, so this is exact. -/
def step9 (cur : List ℕ) : List ℕ :=
  ((List.range (cur.length + 2)).map (R fun i ↦ cur.getD i 0)).rdropWhile (· = 0)

def traj9 : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => let t := traj9 n; t ++ [step9 (t.getLastD [])]

end BMOVet

open BMOVet in
#eval IO.println <| String.intercalate "\n" <|
  ((List.range 300).map fun n ↦ s!"a7 {n} {a7 n}") ++
  ((traj9 400).zipIdx.map fun (c, n) ↦ s!"x9 {n} {",".intercalate (c.map toString)}")
