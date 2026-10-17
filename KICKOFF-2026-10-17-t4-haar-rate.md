# KICKOFF 2026-10-17: T4, the Haar-mean base-3/2 digit rate is below 1/3

Read `notes/36-haar-digit-rate-brw-2026-10-17.md` first.  Setting (Fornet,
`~/src/reservoir/mfornet/antihydra-autoresearch/notes/stationary-cost-variational.md`): on `Z_2`
the legal step is `x ↦ (3x + d)/2` with `d ∈ {0,1,2}`, `d ≡ x (mod 2)`, cost `d`; `V_N(x)` is the
least cost of a legal length-`N` word from `x` and depends only on `x mod 2^N`;
`A_N = 2^{−N} Σ_{x mod 2^N} V_N(x)`, `a_* = lim A_N/N = inf A_N/N`.  Known rigorously:
`0.3042471157… ≤ a_* ≤ 0.36661`.  Open there: whether `a_* ≥ 1/3`.  Notes/36's exact data
(N ≤ 33) fit `a_* = c* = 0.3042471158` with the Aïdékon correction, no free parameter.

**Goal: prove `a_* ≤ c` for an explicit `c < 1/3`** (for example `c = 0.32`), by the truncated
second moment.  New math lane.  Equality `a_* = c*` is the stretch.

## Targets, in order

1. **Paper proof** in `notes/37-haar-rate-second-moment-2026-10-17.md`, claims tagged
   Lean / paper / computed with confidence.  Outline (notes/36 §4): fix θ with tilted mean cost
   `c(θ) < 1/3`; restrict the partition function `Z_N(x; e^{−θ})` (Fornet PT1.1) to words whose
   running cost stays under a linear barrier; bound its second moment by summing over the depth
   `j` where two words diverge.  Key structure: after divergence the two states differ by a
   deterministic 2-adic `δ`, and siblings take opposite parities at the next step (the exact
   second moments in notes/36 §3 are below the iid model's).  Then Paley–Zygmund gives
   `Pr(V_N ≤ cN + o(N)) ≥ ε`; upgrade to `a_* ≤ c` by subtree restarts or Fornet's almost-sure
   constancy (`integrable-dual-boundary.md` ID).  If the pair sum does not close, find the exact
   obstruction and write it down; a sharp negative is a result too.
2. **Lean finite core.**  New module `lean/Collatz/Antihydra/HaarDigitRate.lean`: the legal step
   and cost, `V N : ℕ → ℕ` on residues mod `2^N` (with the Bellman recurrence as a theorem),
   `Z N θ`, and a finite Paley–Zygmund over `Finset.range (2^N)`.  Faithfulness anchor: `V` agrees
   with Fornet's `V_N` definition (cite their `lean/` file if one exists; grep it), and a small
   value check (`2^4 A_4 = 31`, `2^8 A_8 = 936`, by `decide`; no `native_decide`).
3. **Lean main step**, if target 1 closed: the truncated second-moment inequality, then
   `a_* ≤ c` in the finite form "for all large `N`, `Σ_x V_N(x) ≤ (c + ε) N 2^N`".

## Rules

No `native_decide`, no new axioms; Lean lines ≤ 100 chars; commit after each target.  Do not edit
other notes.  Fornet's repo is read-only reference: cite paths, never copy their Lean (import or
re-prove).  Do not commit `tmp/`.  Handoff: `HANDOFF-t4-haar-rate.md`.  Signal `box done` when
target 2 is green and target 1 is either proved or reduced to a precisely stated obstruction.
