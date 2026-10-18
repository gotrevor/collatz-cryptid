# Handoff: Goodstein Turing-machine halting

Branch `wip/goodstein-tm-lean`.  Operator plan: `GOODSTEIN-TM-NEXT.md`.  Scoped completion target:
`sorry-free:lean/Collatz/GoodsteinTM`.

## Checkpoint (2026-10-18, lap 6 review)

The fresh review found a route-significant omission in lap 5: `compareParent_reaches` handled only
a candidate immediately adjacent to `T`.  That is true for the first candidate, but false after a
rejection: restored `P d^k` blocks remain between the next candidate and `T`.  The frozen
statements have not drifted, and the overall hydra/simulation route remains valid, but the macro
proof must use the new generalized comparison lemmas below rather than the adjacent-only wrappers.

Route item 3 now has the complete one-candidate comparison/retry invariant in
`lean/Collatz/GoodsteinTM/Sim.lean`:

* `comparePairThrough_reaches` proves a pairing circuit through an arbitrary unmarked encoded
  middle segment; `comparePairsThrough_reaches_exhausted` iterates it.
* `compareExhaustedThrough_reaches_parent` and `compareParentThrough_reaches` prove the successful
  parent branch with any list of already-rejected encoded nodes between the candidate and `T`.
* `stepN_scanLeftMap`, `restoreD`, and `notParent_reaches_candidate` formalize restoration by
  `NOTPARENT`.
* `compareEqualThrough_reaches_retry` handles the equal-depth `CMP_LCHK` rejection exit;
  `compareDeeperThrough_reaches_retry` handles the strictly-deeper `CMP_L` exit.
* `compareRejectedThrough_reaches_retry` unifies both cases, and
  `candidateRejectedThrough_reaches_retry` composes `CAND_FIND` with the whole comparison and
  restoration loop.  Its result prepends the restored candidate to the encoded middle segment,
  which is the induction invariant needed for repeated retries.

The generated/frozen files and the three frozen statements in `Halts.lean` remain unchanged.  The
scoped target still has exactly one `sorry`, at `halts_of_wf`.

## Verification

* `lake env lean lean/Collatz/GoodsteinTM/Sim.lean`
* `lake build Collatz.GoodsteinTM.Sim Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Sim --axioms GoodsteinTM.compareParentThrough_reaches`
* `~/personal/bin/lean-green . --target Collatz.GoodsteinTM.Halts --import
  Collatz.GoodsteinTM.Sim --axioms GoodsteinTM.candidateRejectedThrough_reaches_retry`

All are green; the real gate ends `FORMALIZE-TIER GREEN` and reports only the intended
`halts_of_wf` proof debt.  Both focused axiom gates report exactly
`[Classical.choice, Quot.sound, propext]`.

## Current blocker and next attack

The remaining crux is the rest of route items 3–6.  The local comparison loop is closed for one
candidate, including arbitrary intervening encoded nodes.  What remains at this front is the
semantic induction that identifies and traverses the whole suffix before the rightmost parent.

Next, in order:

1. Prove a rightmost-parent decomposition for a nonempty `WF` sequence ending in depth `k > 1`:
   split the prefix at its last `k - 1`, and show every encoded node after it has depth at least
   `k`.  Phrase the suffix so `candidateRejectedThrough_reaches_retry` can be iterated from right
   to left while accumulating exactly `treeCells middle`.
2. Compose that induction with `compareParentThrough_reaches` to reach `PAR_END` for the actual
   parent.  Do not fall back to `compareParent_reaches`; its adjacent-only statement is too weak
   for a nontrivial suffix.
3. Continue through `PAR_END/ERASE_L/MARK_END/UNMARK_S` to the canonical `REP_START` copy-block
   configuration.

Do not revisit the hydra order or parser unless a concrete simulation lemma exposes an encoding
mismatch.  The worktree's untracked `CLAUDE.local.md` predates this track and must not be committed.
