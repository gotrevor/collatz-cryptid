import Collatz.BB
import Collatz.BB.SideTape
import Collatz.BB.Multistep

/-!
# TM proof tactics

Lean 4 ports of `busycoq`'s `Individual.v` tactics: `prove_step`, `step`,
`execute`, `follow`, `finish`, `triv`. Together they make the BB(3,3)
holdout proof scripts translate roughly line-for-line from Coq.

The tactics:

* `tm_step_eq` — close a `step2 M c = some c'` goal by computing the
  transition table.
* `tm_finish` — close a trivial `c -[M]->* c'` goal where both sides
  match (`refl` after stream-equality simplification).
* `tm_step` — advance one TM step in a `c -[M]->* c'` or `c -[M]->+ c'`
  goal, leaving the new tail goal.
* `tm_execute` — repeat `tm_step` (then try `tm_finish`) until the goal
  no longer reduces.
* `tm_follow h` — apply a multistep lemma `h : c1 -[M]->* c2` as a
  prefix, transforming `c -[M]->* c3` into `c2 -[M]->* c3` (with
  `c = c1` verified by `rfl`).
* `tm_triv` — exhaustive try: `tm_step`, `tm_follow` (from context),
  `tm_finish`.
-/

namespace BB

/-! ### Tactics -/

/-- Close a `Step2 M c c'` goal where `c` is concrete, leaving `c'` to
be determined by the computation. `rfl` after `unfold` unifies. -/
macro "tm_step_eq" : tactic =>
  `(tactic| (show step2 _ _ = _; rfl))

/-- Close a trivial `c -[M]->* c` goal (refl, modulo stream-equality
simplifications). Silently succeeds if there are no remaining goals. -/
macro "tm_finish" : tactic =>
  `(tactic| (
    try exact Multistep.refl _
    try (refine Multistep.refl ?_; ext <;> simp [repeatList])
    try rfl))

/-- Advance one TM step on a `c -[M]->* c''` goal. The intermediate `c'`
is forced by `rfl` reducing `step2 M c`. Uses `apply` so the implicit
arg `c'` stays a metavariable until `tm_step_eq` pins it via `rfl`.
After stepping, simplifies the resulting goal so the next `tm_step`
can pattern-match. Includes `dirL_blank`/`dirR_blank`/`cons_s0_blank`
so blank-edge patterns collapse to a single `blank` form. -/
macro "tm_step" : tactic =>
  `(tactic| (
    apply Multistep.step
    · tm_step_eq
    try simp only [Side.head_cons, Side.tail_cons,
      Cfg2.dirL_blank, Cfg2.dirR_blank,
      Side.cons_s0_blank, Side.tail_blank, Side.head_blank,
      Side.repeatList_zero, Side.repeatList_nil]
    try tm_finish))

/-- Step until stuck; try to close at the end. -/
macro "tm_execute" : tactic =>
  `(tactic| (
    repeat (first | tm_step)
    try tm_finish))

/-- Like `tm_step` but for a `c -[M]->+ c''` goal: takes the first concrete
step via `MultistepPlus.trans_left`, leaving a regular `Multistep` goal
that subsequent `tm_step`s can close. -/
macro "tm_step_plus" : tactic =>
  `(tactic| (
    apply MultistepPlus.trans_left
    · tm_step_eq
    try simp only [Side.head_cons, Side.tail_cons,
      Cfg2.dirL_blank, Cfg2.dirR_blank,
      Side.cons_s0_blank, Side.tail_blank, Side.head_blank,
      Side.repeatList_zero, Side.repeatList_nil]))

/-- `tm_follow h` chains a multistep lemma `h` onto the prefix of the
current `c -[M]->* c3` goal. Normalizes the new goal LHS by unfolding
`Cfg2.dirL`/`dirR` plus the standard cons/blank simp lemmas — so the
next `tm_step`/`rw` sees a clean struct without nested projections. -/
macro "tm_follow" h:term : tactic =>
  `(tactic| (
    refine Multistep.trans $h ?_
    try simp only [Cfg2.dirL, Cfg2.dirR,
      Side.head_cons, Side.tail_cons,
      Side.cons_s0_blank, Side.tail_blank, Side.head_blank,
      Side.repeatList_zero, Side.repeatList_nil]))

/-- `tm_follow_plus h` chains a positive multistep `h` and switches the
goal to a regular multistep. -/
macro "tm_follow_plus" h:term : tactic =>
  `(tactic| (refine MultistepPlus.trans_right ?_ $h))

end BB
