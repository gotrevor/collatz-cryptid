# Handoff 🤝

**Last session**: 2026-05-26 late evening (`V6KPos.lean` lands: strengthened invariant `InvB` with 9 b-counter clauses, sorry-free; `k_pos_orbit_of` is a sorry-free reduction; `k_pos_orbit` factored to 2 named cascade obligations, each a single sorry).
**Previous**: 2026-05-26 evening (`V6Rule.lean` closed sorry-free; V6 ↔ Shawn bijection found; V6 k_pos identified as the remaining open content).
**Earlier**: 2026-05-25 night (v5/v6 pure rule; 1B-cycle empirical no-halt).
**Branch**: `init`.
**Build**: `cd lean && lake build` — clean, **3 sorry warnings** in default build (Tao, Korec, Bigfoot.sim). Default build does NOT include V6Rule or V6KPos (not in `Collatz/Bigfoot.lean` imports). Explicit `lake build Collatz.Bigfoot.V6KPos` adds 2 cascade-obligation sorries (`k_at_9_ge_2_orbit`, `k_at_3_ge_2_orbit`).

**🌟 START HERE (for next session)**:
1. Read [`BIGFOOT-HANDOFF.md`](BIGFOOT-HANDOFF.md) — comprehensive Bigfoot writeup (669 lines): the machine, V6 recurrence, bijection to Shawn, 11-clause InvB, cascade structure, b mod 12 → terminus map, empirical findings, next-swing options. **This is the canonical reference for resuming Bigfoot work.**
3. Then `notes/18-v6-k-pos-attempt.md` — by-hand cascade analysis.
4. Then `lean/Collatz/Bigfoot/V6KPos.lean` — strengthened invariant (11 clauses) + factored open obligations.
5. **Current state**: the open content of Bigfoot is precisely 2 Lean sorries (`k_at_9_ge_2_orbit`, `k_at_3_ge_2_orbit`) plus the V6 ↔ TM correspondence (still unformalized). InvB has 11 sorry-free clauses including parity + (P1, 3, 5) and (P1, 6, < 6) ruled out.
6. **Next swing options** (in order of attractiveness):
   - (a) **Keep chipping the cascade**: add `p1_a9_b_ge_27`-style state-specific bounds. Each new clause rules out a few specific dangerous cases. Doesn't close sorries but tightens the danger surface incrementally.
   - (b) **Pivot to V6 ↔ TM correspondence** (independent of k_pos). Required regardless to close Bigfoot, and might give insight into the structure.
   - (c) **Lyapunov function search**: try `phi(s) = 2k + f(a%M, b%M, pat)` for various M. The b mod 12 → terminus map is a strong hint; haven't fully exhausted.
   - (d) **Trajectory-aware invariant**: prove "between any two decrements, k recovers" — hard but maybe possible with the pairing structure.

## Today's contribution (2026-05-26 late)

**`lean/Collatz/Bigfoot/V6KPos.lean`** (~510 lines, 2 sorries — both in named theorems below):

- `InvB` — 11-clause strengthened invariant: 4 from `Inv` (no_halt's invariant) + 6 new structural b-counter clauses + parity.
  - `p2_b_ge_2`, `p2_b_le_3`: P2 b is in {2, 3}.
  - `p2_b2_a_ge_7`: P2 with b=2 has a ≥ 7 (only Q-same outputs b=2, and its output a = b_in + 7 ≥ 7).
  - **`p1_a3_b_ge_7`** (was `p1_a3_b_ge_5`): D-W input b ≥ 7. Rules out (P1, 3, 5) — the smallest dangerous-mod-12 D-W input.
  - `p1_a2_b_ge_7`: W input b ≥ 7.
  - **`p1_a6_b_ge_6`** (new): supports the `p1_a3` strengthening by ruling out the S source `(P1, 6, 0)`.
  - **`parity_ab`**: `(s.a + s.b) % 2 = 0`. Every rule's `Δ(a+b) ∈ {0, 2, 4}`. Verified empirically over 100M cycles with zero violations.
- `InvB_initial`, `step_preserves_InvB`, `orbit_InvB` — sorry-free.
- `k_pos_orbit_of` — sorry-free reduction: assuming `k ≥ 2` at every reachable `(P1, a=9)` and `(P1, a=3)`, derive `k ≥ 1` at every orbit state.
- `k_at_9_ge_2_orbit`, `k_at_3_ge_2_orbit` — the two open cascade obligations. Each is one `sorry` with a docstring explaining what they mean and pointing to `notes/18-v6-k-pos-attempt.md`.
- `k_pos_orbit` — derived from `k_pos_orbit_of` plus the two cascade theorems.

**`tools/sandbox/bigfoot_v6_kpos_analysis.py`** (~190 lines):
- Empirical analyzer for the V6 orbit's k-trajectory and decrement-rule firings.
- Confirms parity invariant (0 violations at 100M cycles).
- Tabulates `b mod 12` histograms at D-W and B-coll firings.
- Reports k extremes (`k ∈ [2, 16]` over 100M cycles) and max consecutive
  decrements (= 2; always recovers before a third).

**`tools/sandbox/bigfoot_v6_reach_map.py`** (new, ~80 lines):
- Maps reachable `(pat, a, b mod M)` residues and `k_min` per (pat, a)
  for small a over the orbit.
- Findings: at (P1, a=3): b mod 12 ∈ {1, 3, 5, 7, 9}; at (P1, a=9):
  b mod 12 ∈ {1, 3, 9, 11}. Many (P2, a) for small a have ZERO visits
  (e.g., (P2, 10), (P2, 13)) — empirical evidence for unreachability
  facts useful in cascade analysis.

**Why this factoring matters**: the open content of Bigfoot is now expressed in V6 coords as TWO precisely-stated `∀ n s, …`-shaped Lean obligations, with a sorry-free reduction from them to `k_pos`. The cascade analysis from `notes/18` corresponds directly to these two theorems: extending `InvB` with `k_at_*_ge_2` clauses (cascading backward from a=9 and a=3) is a concrete path to closing them in Lean.

**Minor file edit**: `V6Rule.lean`'s `step_X` per-rule unfolding lemmas changed from `private lemma` to `lemma` (no semantic change) so `V6KPos.lean` can reuse them.

The rest of this document is the previous session's handoff (2026-05-25), retained for context.

---

## Current state (one-screen view)

```
Phase A (Collatz core)              ✅ Basic, Conjecture, Conditional, OrbitMin   [no sorry]
Tao 2019 framework                  ✅ LogDensity defs + Tao statement            [statement-only sorry]
Korec 1994 framework                ✅ Korec statement inside AlmostAllPos        [statement-only sorry]
BB framework                        ✅ Own BB.lean (not mathlib's TM0)            [no sorry]
Bigfoot reduction interface         ✅ Reduction struct + glue (toNeverHalts)     [no sorry]
Bigfoot encoding                    ✅ bigfootEnc, anchored coords, cell-verified [no sorry]
Bigfoot cost function               ✅ 24·c + 176 (Quick_Sim Diff Rule 0)         [no sorry]
Bigfoot bootstrap                   ✅ stepN 69 blank = some (bigfootEnc init)    [no sorry]
Bigfoot sim                         🚧 PARKED in Lean                             [sorry; rule found in Python]
Bigfoot (k, a, b) recurrence (v6)   ✅ 9-rule closed form, no-halt at 1B cycles   (see notes/17)
Bigfoot V6 in Lean (V6Rule.lean)    ✅ Inv + step preserves Inv + no_halt          [no sorry]
Bigfoot V6 strengthened (V6KPos)    ✅ InvB (9 clauses) + k_pos_orbit_of           [no sorry — reduction]
Bigfoot V6 k_pos (cascade)          🚧 2 named obligations open                    [k_at_9_ge_2, k_at_3_ge_2]
Bigfoot Python rewrite v1→v6        ✅ literal → macro → ... → tape parser → rule (see notes/16, 17)
Holdout 153 reduction               ❌ refuted (4-counter conjecture)
Holdouts 397, 531 (factor complex.) ✅ shape-explosive, bounded factor complexity
531 finite-reachable hypothesis     ❌ refuted (10M-loop saturation)
397 PDA sweep + linear +0.5/cycle   ✅ confirmed at 2.5M loops, R²=0.9999
397 clean (a,b,c) reduction         ❌ refuted (97% unique peak bootstraps; notes/15)
BB(6) batch deciders                ✅ 0/1085 decided (community-known result reproduced)
```

Sorries in the Lean repo (3 in default build, 3 more in explicit-build files):
1. **`Collatz.tao2019`** in `lean/Collatz/Tao.lean` — statement-only.
2. **`Collatz.korec1994`** in `lean/Collatz/Korec.lean` — statement-only.
3. **`Collatz.Bigfoot.bigfootReduction.sim`** in `lean/Collatz/Bigfoot/Reduction.lean` — parked.
4. **`Collatz.Bigfoot.invariantA_sorry`** in `lean/Collatz/Bigfoot/InvariantSketch.lean` — Shawn-coords version of the open question. Experimental file.
5. **`Collatz.Bigfoot.V6.k_at_9_ge_2_orbit`** in `lean/Collatz/Bigfoot/V6KPos.lean` — V6-coords cascade obligation #1 (B-coll). **The genuinely open question** (4 + 5 + 6 together close BB(3,3)'s Bigfoot cryptid via the V6 ↔ Shawn bijection in `bigfoot_bijection_check.py`).
6. **`Collatz.Bigfoot.V6.k_at_3_ge_2_orbit`** in `lean/Collatz/Bigfoot/V6KPos.lean` — V6-coords cascade obligation #2 (D-W). **The genuinely open question** (the harder of the two).

## Why `sim` is parked

Trevor's question (2026-05-25): "Would this actually prove anything new?" Answer: **No.** `sim` would be formalization of Ligocki's published reduction (the (a,b,c) parametric dynamics ↔ Bigfoot TM correspondence). Mechanical verification. ~weeks of real Lean work.

The genuinely open question is **`Bigfoot.Hypothesis`** itself — that the (a,b,c) orbit never reaches the halting branch (`a = 0 ∧ b % 6 = 2`). Empirically verified for astronomical iteration counts; mathematically unproven. Proving it would close BB(3,3).

Sim is left as a clearly-typed obligation. The interface, encoding, cost, bootstrap, and glue are all done — sim is the one remaining piece.

## Today's arc (2026-05-25 evening + late session)

1. **Lean: `Korec 1994` stated.** `Collatz.korec1994` inside `AlmostAllPos` framework — strongest pre-Tao "almost all" result. Proof skeleton documented inline. Commit `d6303ba`.

2. **397 substitution hunt (refuted) → PDA sweep finding.** notes/14 written: 100% boundary edits, 100% strict push/pop alternation across 624 cycles, +0.5/cycle linear growth at R²=0.998.

3. **397 calibration burn.** Streaming Quick_Sim to 2.5M loops (~78 min CPU). Confirms linear growth: slope 0.4992, R²=0.998 push / R²=0.9999 pop. 12 head states locked, no new phenomena. Killed at 2.5M.

4. **397 deep inspection refutes clean (a,b,c).** notes/15: 623 sweep-reversal snapshots show peak bootstrap is 97% unique per cycle. Updated case split: 15% Bigfoot-shaped / 40% bounded counter automaton / 35% strictly harder. Memory `feedback_research_claims_rigor.md` extended with episode 4.

5. **Bigfoot Python rewrite v1→v4** (notes/16). Stepwise decompilation; each version equivalence-checked against v1. v4 surfaces Bigfoot's `(a, b, c)` integer-state signature in raw data: bites are 98.3% zero, non-zero bites form APs within a cycle, N (dance bounce-count) is near-period-10. Commit `8524b3b`.

6. **Bigfoot v5 (tape parser) → v6 (pure rule)** (notes/17). Continued the rewrite series:
   - **v5 (`bigfoot_v5_tape_inspect.py`)**: dumps RLE tape at super-cycle boundaries; reveals `(1 2)^k 1^a 2^b TAIL` shape with two end-cases (P1 / P2).
   - **v5 extractor (`bigfoot_v5_extract.py`)**: parses (k, a, b, pattern) per cycle. Right-to-left parsing avoids `(1 2)^k | 1^a` ambiguity.
   - **v5 stress (`bigfoot_v5_stress.py`)**: predicts each cycle from a candidate rule, catches anomalies. Initial 200-cycle conjecture missed `B-coll` (a=9) and `Q-W` (a=7) — surfaced at 10k cycles.
   - **v6 (`bigfoot_v6_pure_rule.py`)**: pure rule iterator (no TM). Verified against v5 at 996 cycles. Pushed to 1,000,000,000 cycles in 167s — no halt, no anomalies.
   - **Recurrence**: 9 rules on (k, a, b, P1/P2) state. S/B alternation dominates; wraps are exponentially rare (110 wraps total over 1B cycles).

7. **Bigfoot Hypothesis formalization attempt** (`lean/Collatz/Bigfoot/InvariantSketch.lean`). Switched to Shawn's existing `Dyn` rule (which is the cleaner 6-case form). Proved:
   - `step_eq_none_iff`: `Dyn.step d = none ↔ d.a = 0 ∧ d.b % 6 = 2`. (Decidable.)
   - `orbit_none_implies_halt_state`: the orbit reaches `none` only via the halt configuration.
   - `c_eq_two_after_r2`, `no_three_consecutive_r2`: **streak bound** — after two r=2 events, the third state has b%6 ∈ {1, 3, 5}, never 2. Three consecutive r=2 steps are impossible. (Provable by direct case analysis on `(8k+5) mod 6`.)
   - `hypothesis_of_invariantA`: factors out the open question. If `∀ n d, orbit n = some d → d.b % 6 = 2 → d.a ≥ 1`, then `Hypothesis`.
   - **Open**: `invariantA_sorry`. This is the genuine open content. Empirical: 1M-step direct Shawn-orbit + 1B-cycle (k,a,b) coordinate both show no halt-precursor reached.
   - Auxiliary `bigfoot_shawn_rule.py` + `bigfoot_shawn_invariant.py` (sandbox): Shawn-rule simulator + streak/min-a analyzer. `a` grows linearly at rate ~1/6 per step; `a` never reaches 1 or 2 at r=2 events in 1M.

## Where to start next

The TOP priority — also Trevor's explicit ask at end of last session — is the **(k, a, b) Lean proof attempt**. Detailed below.

Other moves stay ranked as before but are SECONDARY now.

## TOP MOVE: full Lean proof of no-halt in (k, a, b) coords 🎯

### Background

After completing v6's empirical verification (1B cycles, no halt) and writing `InvariantSketch.lean` in Shawn's (a, b, c) coords, Trevor pushed back:

> "Seems like little true progress here. Are we close to an invariant Ligocki didn't already have? Have we learned anything from the Python that might teach us something 'structural', not empirical?"

The honest answer ended this session: **possibly yes, in MY (k, a, b) coords**. The argument:

```
Goal:    P1(a=0) is unreachable from initial state.

Step 1:  P1(a=0) only produced by P2→P1 with a_p2 = 4.
         [Case analysis: enumerate rules outputting P1, see which can give a=0.]

Step 2:  a_p2 = 4 in P2 only produced by Q-kpp at P1(a=1, b=4).
         [Q-same gives a_p2 = b+7 ≥ 7; only Q-kpp can give a_p2 = 4 if b=4.]

Step 3:  Every reachable P1(a=1, b) has b ≥ 5.
         [Case analysis: 3 rules produce P1(a=1, _):
             - S from P1(a=4, b-5)   → b = (b-5)+5 ≥ 5
             - B-coll from P1(a=9, b-12)  → b ≥ 12
             - P2→P1 from P2(_, 5, 3) → b = 7  ]

Step 4:  Therefore P1(a=1, b=4) unreachable, so P2(a_p2=4) unreachable,
         so P1(a=0) unreachable.  No halt.
```

This is **finite backward case analysis on the 9 rules** — no Collatz-like reasoning over a multiplicatively-growing variable. **Genuinely structural**, not empirical.

### Why this is potentially new

Shawn's (a, b, c) rule has `b` growing by ~4/3 per step (Collatz-flavored). Reasoning by `b mod M` doesn't reduce to finite-state dynamics, so the no-halt invariant is intrinsically global.

My (k, a, b) rule has `b` growing **linearly** (by ≤ 12 per step). Each rule's input/output relationship is **bounded** in `(a, b)` space. So backward case analysis terminates.

### What's left to be rigorous

The proof sketch above is convincing IF we can also handle the **k-bound caveat**: rules `B-coll` and `D-W` decrement k by 1. For them to be well-defined in ℕ, we need `k ≥ 1` at every firing.

Empirically, `k ≥ 2` throughout the 1B-cycle orbit. But that's empirical. To make it rigorous:

#### Obligation A: encode the rule in Lean

New file: `lean/Collatz/Bigfoot/V6Rule.lean`. Define:

```lean
inductive Pat | P1 | P2
structure State where
  k : ℕ
  a : ℕ
  b : ℕ
  pat : Pat
def step (s : State) : Option State := ...    -- the 9-rule table
def initial : State := ⟨2, 1, 5, P1⟩
def orbit : ℕ → Option State | 0 => some initial | n+1 => (orbit n).bind step
```

#### Obligation B: state the invariant

```lean
structure Inv (s : State) : Prop where
  k_pos      : s.k ≥ 1           -- ! caveat: needs proving, see below
  p1_a_pos   : s.pat = P1 → s.a ≥ 1
  p1_a1_b5   : s.pat = P1 ∧ s.a = 1 → s.b ≥ 5
  p2_a_5     : s.pat = P2 → s.a ≥ 5
```

Plus possibly more:
```lean
  p2_a5_b3   : s.pat = P2 ∧ s.a = 5 → s.b = 3
```
(This is the "P2 with a_p2=5 always has b_p2=3" auxiliary needed for P2→P1's preservation of `p1_a1_b5`.)

#### Obligation C: prove `Inv(initial)`

Should be `decide` or `simp` — initial state is `(2, 1, 5, P1)`.
- k_pos: 2 ≥ 1 ✓
- p1_a_pos: 1 ≥ 1 ✓
- p1_a1_b5: 5 ≥ 5 ✓
- p2_a_5: vacuous

#### Obligation D: prove step preserves Inv

Case analysis on which of the 9 rules fires. For each:

- **S** (P1, a even, a ≥ 4):  Output `(k, a-3, b+5, P1)`.
  - k_pos: trivial (k unchanged).
  - p1_a_pos: a-3 ≥ 1 since a ≥ 4. ✓ (omega).
  - p1_a1_b5: if a-3 = 1 then a = 4, and output b = b+5 ≥ 5. ✓
  - p2_a_5: vacuous.

- **B** (P1, a odd, a ≥ 11):  Output `(k, a-9, b+11, P1)`.
  - a-9 ≥ 2, never 1. So p1_a1_b5 vacuous.
  - Other clauses straightforward.

- **B-coll** (P1, a = 9):  Output `(k-1, 1, b+12, P1)`.
  - **k_pos**: needs `k ≥ 2` input to give k-1 ≥ 1 output. **OPEN.**
  - p1_a1_b5: 1, b+12 ≥ 12 ≥ 5. ✓

- **Q-W** (P1, a = 7):  Output `(k+1, b+7, 0, P1)`.
  - k_pos: trivially preserved.
  - p1_a_pos: b+7 ≥ 7 ≥ 1. ✓

- **W** (P1, a = 2):  Output `(k, b+4, 0, P1)`.
  - p1_a_pos: b+4 ≥ 4. ✓

- **D-W** (P1, a = 3):  Output `(k-1, b+7, 0, P1)`.
  - **k_pos**: needs `k ≥ 2` input. **OPEN.**

- **Q-same** (P1, a = 5):  Output `(k, b+7, 2, P2)`.
  - p2_a_5: b+7 ≥ 7 ≥ 5. ✓
  - Auxiliary if tracking p2_a5_b3: b+7 = 5 ⟹ b = -2 impossible, so vacuous. ✓

- **Q-kpp** (P1, a = 1):  Output `(k+1, b, 3, P2)`.
  - p2_a_5: a_p2 = b. Need `b ≥ 5`. **Uses p1_a1_b5 input** ✓ (inductive hypothesis).
  - p2_a5_b3: if b = 5 then output is `(k+1, 5, 3, P2)`, b_p2 = 3 ✓.

- **P2→P1** (P2):  Output `(k, a_p2-4, b_p2+4, P1)`.
  - p1_a_pos: a_p2 - 4 ≥ 1 ⟸ a_p2 ≥ 5 ⟸ p2_a_5. ✓
  - p1_a1_b5: if a_p2-4 = 1 then a_p2 = 5; by p2_a5_b3, b_p2 = 3, so output b = 7 ≥ 5. ✓
  - **k_pos**: k unchanged.

**Result**: every clause goes through CLEANLY except `k_pos` at B-coll and D-W.

#### Obligation E: the k_pos gap — three possible paths

##### Path 1 (optimistic — finite case analysis)

Show that B-coll fires only when k ≥ 2, and D-W fires only when k ≥ 2.

Claim: `Reachable P1(k, 9, _) → k ≥ 2`. Proof attempt:
- `a = 9` produced only by `S` from `a = 12`. So `P1(k, 9, b)` came from `P1(k, 12, b-5)` via S.
- `a = 12` produced by: S from `(k, 15, _)`, B from `(k, 21, _)`, or others.
- Continue tracing backward...
- Hope: every reachable `(k, 9, _)` comes from a chain that started with `k ≥ 2` and never lowered k below 2.

This MIGHT terminate as finite case analysis. Or it might not (if there's a self-referential cycle on small k).

##### Path 2 (pragmatic — stronger inductive invariant)

Add to `Inv`:
```lean
  k_at_9 : s.pat = P1 ∧ s.a = 9 → s.k ≥ 2
  k_at_3 : s.pat = P1 ∧ s.a = 3 → s.k ≥ 2
```

Then `k_pos` follows from these locally. Preservation analysis:
- When does the orbit reach `(_, 9, _)`? After an S from `(k, 12, _)`. Need to show `k_at_12 → k ≥ 2`.
- Cascade back: `k_at_a → k ≥ ?` for all a that can transition into a=9 or a=3.
- Hope: the cascade stabilizes — some finite chain of "if a hits X, k must be ≥ Y" implications.

##### Path 3 (fallback — accept the obligation)

Leave `k_pos` as a sorry with a precise statement:

```lean
theorem k_at_collapses (s : State) (h : Reachable s)
    (hp : s.pat = P1) (ha : s.a = 9 ∨ s.a = 3) : s.k ≥ 1 := sorry
```

This is still a contribution: it factors `Hypothesis` into a precise, FINITE-flavored statement (no infinite-orbit reasoning).

#### Obligation F: connect to existing Lean

Once V6Rule.lean is built and the no-halt theorem proved:

1. Show my `step` is equivalent to Shawn's `Dyn.step` (composed appropriately for the cost-function granularity). OR show that my orbit and Shawn's both correspond to the same TM dynamics.

2. Discharge `Bigfoot.bigfootReduction.sim` using my rule's correspondence to the TM.

3. The chain: `MachineNeverHalts ⟸ Reduction.toNeverHalts ⟸ Hypothesis ⟸ no-halt-of-my-rule`.

### What's the worst case

Even if path 3 is the only viable one for `k_pos`, the contribution is:

- **Empirical recurrence**, 1B-cycle verified, in clean coordinates.
- **Lean encoding** of the rule.
- **Proof of no-halt MODULO `k_at_collapses`**.
- **Identification of the precise remaining obligation** as a finite-flavored claim about reachability of specific (k=1, a=9, b) or (k=1, a=3, b) states.

That last point is what would make this contribution NEW: even Shawn doesn't seem to have a Lean-style precise factoring of where the hardness lives.

### Order of operations for the next session

1. **Verify the (k, a, b) rule is equivalent to the TM** before doing more Lean work. Right now we have v6 ≡ v5 ≡ v1 (via the rewrite chain). If anything's wrong with v6, the proof is moot. (Sanity check at 1000+ cycles is sufficient; already done.)

2. **Write `V6Rule.lean`** — basic encoding, then state Inv and `step_preserves_Inv` skeleton.

3. **Discharge the 8 cases that don't touch k**. These are clean omega-level proofs.

4. **Identify exactly which case (B-coll or D-W) breaks `k_pos`**, then decide between paths 1, 2, 3.

5. **Don't get lost in Shawn's coordinates** for this attempt. Use my (k, a, b) directly. Connect to existing Lean at the end, via Reduction.sim.

### Reference

Full session detail is in the author's private working notes; the load-bearing
content is reproduced in `BIGFOOT-HANDOFF.md` and `notes/17`.

## Other moves (secondary now)

3. **Match coordinates to Shawn Ligocki's published (a, b, c).** Find his exact reduction and write the change-of-variables. Once matched, we can cite his work directly.

4. **Apply v5-style rewrite series to other holdouts.** notes/15 already showed 397's bootstrap is 97% unique per cycle, suggesting 397 doesn't have a clean (a, b, c). But the v5 approach gives a sharper test — does the parser succeed at all? Worth trying on 153 and 531 too.

5. **397 case discrimination (Task #7 pending).** Run Quick_Sim to 10M loops with reversal-aware snapshots; compute valley-bootstrap novelty curves per head signature out to ~30k cycles. If curves flatten → case 2.5 (decidable counter automaton). If keep growing → case 3 (harder than Bigfoot). ~3-5 hours CPU. Discriminating.

6. **Korec proof attempt.** Three-step skeleton documented in `Korec.lean`: trajectory descent → parity-sequence weighted counting → glue. Korec's original is ~5 pages of elementary density bookkeeping; might be tractable.

Skip:
- Pinging Shawn Ligocki. Trevor protective of the relationship; he'll initiate if appropriate.
- 153 four-counter retry (refuted by trace analysis).
- BB(6) Inductive decider extraction.
- 100M-loop burns on 397.

## Repo layout

```
collatz-cryptid/
├── HANDOFF.md                  # this file
├── README.md
├── species.py, stopping.py     # early Collatz exploration (pre-Lean)
├── data/refs/                  # local-only PDF library (gitignored; see notes/refs.md)
├── lean/                       # Lean 4 + mathlib (see lean-toolchain)
│   ├── lakefile.toml, lean-toolchain
│   └── Collatz/
│       ├── Basic.lean          # T, sanity
│       ├── Conjecture.lean     # Collatz.Conjecture : Prop
│       ├── Conditional.lean    # no_nontrivial_cycle, τ_ge_log2
│       ├── OrbitMin.lean       # colMin, conjecture_iff_colMin_one
│       ├── LogDensity.lean     # logSum, logProb, HasLogDensity, AlmostAllPos
│       ├── Tao.lean            # Tao 2019 Theorem 1.3 (statement-only sorry)
│       ├── Korec.lean          # Korec 1994 (statement-only sorry; added today)
│       ├── BB.lean             # own 3-state 3-symbol TM framework
│       ├── Bigfoot/
│       │   ├── Machine.lean, Dynamics.lean, Hypothesis.lean
│       │   ├── Encoding.lean   # bigfootEnc + bigfootCost + bootstrap_full
│       │   ├── Reduction.lean  # Reduction struct + glue + bigfootReduction (sim sorry)
│       │   ├── InvariantSketch.lean  # Shawn-coords version of the open content (experimental)
│       │   ├── V6Rule.lean    # V6 (k, a, b) rule + Inv + no_halt [no sorry]
│       │   └── V6KPos.lean    # InvB + k_pos_orbit_of + 2 cascade-obligation sorries
│       └── Holdout153/
│           ├── Machine.lean, Hypothesis.lean
├── notes/                      # per-topic .md, 01..17
│   ├── 14-holdout-397-pushdown-sweep.md        # PDA confirmed; partial supersession banner
│   ├── 15-holdout-397-pattern-erosion.md       # supersedes notes/14's (a,b,c) claim
│   ├── 16-bigfoot-rewrite-series.md            # Python v1→v4 stepwise decompilation
│   └── 17-bigfoot-v5-recurrence.md             # v5/v6: closed-form (k, a, b) recurrence
├── sim/                        # Quick_Sim traces, batch CSVs (some .gitignored)
│   ├── 397_burn_500k.* / 397_burn_10M.*       # streaming-burn checkpoints + side files
│   └── 397_reversals.json                      # 623 peak + 623 valley snapshots
└── tools/sandbox/              # project-specific Python
    ├── bb33_397_*.py                          # 9 scripts; see notes/14 and notes/15
    ├── bigfoot_v1_literal.py
    ├── bigfoot_v2_macro.py
    ├── bigfoot_v3_supercycle.py
    ├── bigfoot_v4_dance_internals.py
    ├── bigfoot_v5_tape_inspect.py             # RLE tape dump at boundaries
    ├── bigfoot_v5_extract.py                  # parser + (k, a, b, pat) extraction
    ├── bigfoot_v5_stress.py                   # rule vs simulator at 10k cycles
    └── bigfoot_v6_pure_rule.py                # pure rule iterator, 1B cycles verified
```

## Running things

- **Lean build**: `cd lean && lake build`. ~3s incremental. **3 expected sorry warnings.**
- **Lean check single file**: `lake build Collatz.Korec` (or any specific module).
- **Sandbox scripts**: run `tools/sandbox/*.py` with `uv run` (or any Python 3.12+).
- **Bigfoot Python series**: each VN runs and prints its own self-verification ("PASS" against v1) plus structural observations.
- **Quick_Sim CLI**: `~/.venvs/bb/bin/python ~/src/busy-beaver/Code/Quick_Sim.py [opts] <tm>`. Shawn Ligocki's repo; venv at `~/.venvs/bb` (Python 3.14).
- **Streaming burn on a TM**: `sandbox tools/sandbox/bb33_397_burn.py --max-loops N --out FILE.json`. Writes checkpoints every 500k loops. Per-loop wall-time grows with tape length — at scale of 2-3M loops, total wall-time is ~hours.

## Key references

PDFs are kept **locally only** in `data/refs/` (gitignored).  Links: `notes/refs.md`.

| File | Content |
|---|---|
| tao-2019-almost-all-orbits.pdf | arXiv:1909.03562 v5. Headline modern result. |
| lagarias-2003-survey-1.pdf | arXiv:math/0309224 v13. Annotated Bibliography I (1963-1999). 74pp. |
| lagarias-2006-survey-2.pdf | arXiv:math/0608208 v6. Annotated Bibliography II (2000-2009). 42pp. |
| krasikov-lagarias-2003-density.pdf | arXiv:math/0205002. Density bound `x^0.84`. 21pp. |

Index + Tao's conventions for Lean: `notes/refs.md`. Korec 1994 itself is not held locally — referenced via the Lagarias surveys, which cite it extensively.

## Conventions & gotchas

### Lean
- `BB.Cfg` has `@[ext]`. Without it, `ext` tactic fails on Cfg equality.
- `set_option maxRecDepth N in theorem` does **not** play well with attached `/-- docstring -/`. Use a regular `-- comment` instead.
- `decide` with `maxRecDepth ≥ 2000` works for `BB.stepN N blank` projections (state, pos, tape at specific i) up to N ≈ 69. Tape equality on `ℤ → Sym` is **not** decidable; needs `funext` + position case split.
- `Real.logb` lives in `Mathlib.Analysis.SpecialFunctions.Log.Base`, not `Log.Basic`.
- Cross-checking via `decide`/`#eval` on small projections catches encoding bugs early.

### Git
- Branch `init`; no remote. HANDOFF earlier claimed a pre-commit hook blocks trailing whitespace / CRLF / `main` commits, but no such hook is installed at `.git/hooks/pre-commit` — commits succeed regardless. Still good practice to keep files clean.
- `.gitignore` excludes `lean/.lake/` (build cache, ~7GB) and the 50k/200k-loop complexity traces (~800MB).
- Commit message convention: short prefix, technical body. Co-Authored-By tag for Claude-generated commits.

### Python rewrite chain (Bigfoot)
- Every `bigfoot_v*.py` defines an equivalence check against `BigfootV1` (the canonical literal simulator). Run any version and it prints `verification: PASS -- ok` if its macros match v1's micros bit-exact.
- v4 imports v3 imports v2 imports v1. Each version is callable standalone for analysis.
- If you write v5/v6/..., follow the same pattern: subclass the previous version, override at a higher granularity, add a `verify_v*_against_v1` function, and print its result on `main()`.

### Quick_Sim macro rules for Bigfoot (Diff Rule 0, used for `bigfootCost`)
```
Initial: 00^inf 12^(a+1) 11^(b+7) <A (11) 11^(c+1) 00^inf
Diff:    00^inf 12^0    11^-6   <A (11) 11^8       00^inf
Steps:   24·c + 176, Loops: 27
```
Exact for `b ≥ 7`. Below threshold, micro-step counts vary per case.

## Behavioral notes (Trevor)

- **Don't suggest pinging Shawn Ligocki.** Explicit pushback. Reason: protective of relationship.
- **Honestly distinguish formalization from new math.** Lead with what's novel vs. what's reproduction.
- **Negative results are clean information.** 531 saturation refuted, 397 (a,b,c) refuted — document honestly, don't bury.
- **Calibrate before claiming structure.** A bounded-X finding from a 200k-sample window needs ≥1-2 orders of magnitude more sampling before naming it structural. Different signals need different sample sizes — a 4-sample pattern match isn't a 624-sample regression. **v5 episode reinforces this**: the initial 200-cycle rule conjecture was wrong (missed 2 wrap cases that surfaced only at 10k+). Always push to 10–100× the originating sample size before calling a conjecture solid.
- **Trace-back-to-canonical matters.** Each Python rewrite version VN includes a verifier against v1. Don't break that chain. v6 (pure rule) is verified against v5 (which is verified against v1).

---

🌯 Wrapped 2026-05-25 night (Bigfoot v5 + v6: closed-form (k, a, b) recurrence, no halt at 1B cycles).
