# BMO#9: prove `beaver_math_olympiad_problem_9` by porting the Rocq proof 🦫

**Objective:** close `beaver_math_olympiad_problem_9` in `lean/Collatz/BMO/Problem9.lean`.  The run
stops when `lean/Collatz/BMO/` has no `sorry` left.
**Do not change** the headline statement.  It is transcribed from the BMO wiki §9 in
formal-conjectures style, and it is the anchor for an upstream `formal_proof` link.  It was checked
numerically against the list model for 4000 steps.  Keep the existing `BMO9` list-model lemmas.

**This is a known result, so port it; do not search for a new proof.**  Source: the Rocq proof by
ccz181078, `~/src/busycoq/verify/BMO9.v` (branch `BB6`, commit `605d26d`, 3,819 lines, read-only).
Its endpoint is `TM1.nonhalt : ~halts tm c0`:

```
nonhalt_of_returns ∘ Prefix.single_returns ∘ Closure.G_returns ∘ FinalBudget.budget
```

**The mathematical core is `∀ k, ∃ e m, Prefix.Exec (1+e) [3*k] [m]`:** every singleton `[3k]`
safely returns to a larger singleton.  Port everything that core needs.  **Skip `Module TM1`**
(lines 3652-3819).  It proves the Turing-machine correspondence, and the headline is the wiki's
arithmetic statement, not the machine.

## Module map (line ranges in BMO9.v)

| Rocq module | Lines | Role |
|---|---|---|
| `Prefix` | 7-234 | `Step`/`Run`/`Exec` on finite prefixes, mass, `single_returns` |
| `Block` | 237-592 | summary records, the integer identity, `|θ| ≤ 1/2`, exact descent |
| `Table`, `UniqueTable`, `CheckTable` | 596-1396 | the finite table; `base_structured` checks `k ≤ 65536` by computation |
| `Bridge`, `Finite` | 1398-1505 | glue from the table to the inductive argument |
| `WordArith` … `WordLink` | 1507-2179 | dyadic words `q, 2q, 4q, …`, `library_complete` (index ≤ 2048), `F2` |
| `Phase`, `Cubic`, `Stages`, `BoundaryBound` | 2182-2657 | boundary copying, `steps ≤ 4k³`, stage induction, `returns_of_bound` |
| `Closure` | 2659-2740 | the single induction step: `all_good`, **`G_returns`** |
| `HighPath` … `GlobalBounds` | 2743-3550 | multiscale estimates for indices above 65536 |
| `FinalBudget` | 3552-3650 | **`budget`**: discharges `Closure.budget` for `k > 65536` |

## Route

1. **Bridge first.**  Show the headline follows from the core singleton-return statement, stated
   in a Lean mirror of `Prefix.Exec`.  The existing list model `BMO9.step`/`orbit` is the natural
   middle layer.  Note that Rocq's `Step` compresses the rules (`E`: `2n` heads, `O`: `2n+1` heads).
   Commit with the core as a named `sorry`.
2. **One Lean file per Rocq module**, under `lean/Collatz/BMO/Problem9/`, imported in order.  Port
   statements first with `sorry` bodies, so the dependency skeleton builds green early.  Then fill
   proofs module by module.  A rising sorry count during decomposition is progress.
3. **Computation:** `CheckTable` verifies a table up to 65536 by evaluation.  `native_decide` is
   fine here.  `decide +kernel` is nicer when it is fast enough, but don't fight for it.
4. `lia` ↦ `omega` (ℕ/ℤ linear), `nia` ↦ `nlinarith`/`positivity`, and Rocq `Z` ↦ Lean `ℤ`.

Commit each green checkpoint, and record status at the bottom of this file as you go.

## Status

- 2026-10-01: **Route step 1 done.** `Problem9/Prefix.lean` ports Rocq `Prefix` up to
  `single_returns` (proved).  `Problem9/Bridge.lean` proves the stream recursion simulates
  `Exec` safely (`Bridge.forever`).  The headline is proved modulo one sorry,
  `Closure.G_returns` (`∀ k t, ∃ e m, Exec e (G (k+1) (1+2t)) [m]`).  Not yet ported from Prefix:
  `run_last`, `F_to_G`, `odd_lookup` (needed by `Table`).  Next: skeleton `Block`, `Table`.
- 2026-10-01 (later): ported sorry-free: Prefix (complete), Block, Table, UniqueTable,
  CheckTable (`base_structured` via native_decide, ~3s; P16 matches Rocq), TableBridge
  (= Rocq Bridge+Finite).  Convention: levels/depths/exponents are ℕ, everything else ℤ.
  In flight (subagents): Word{Arith,Relation,Library,Check,Link}; Phase/Cubic/Stages;
  HighPath/Exponential/ScaleNumbers.  Remaining after: BoundaryBound, Closure, WordBlocks,
  Multiscale, SmallScale, LargeStep, GlobalBounds, FinalBudget.
