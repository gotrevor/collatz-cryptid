# Bigfoot 🦶 — V6 k_pos Handoff

**Standing 2026-05-27 morning EDT.** Companion to the project-wide
`HANDOFF.md`; this file focuses entirely on Bigfoot (BB(3,3) holdout #1)
and the V6 (k, a, b) approach. If you're a fresh session, read this
end-to-end; the high-level `HANDOFF.md` has the rest of the cryptid-zoo
context.

> **Session E follow-up (2026-05-26 evening)**: `BB.step_toSide` proved
> sorry-free along with `stepN_toSide`, `stepN2_of_stepN_toSide`, and
> `multistep_toSide` (`lean/Collatz/BB/Iso.lean`). The `Cfg2`/side-tape
> world (where `tm_step`, `tm_follow`, `progress_nonhalt_simple`,
> `multistep_nonhalt` all live) is now interoperable with the ℤ-tape
> `BB.Cfg`/`BB.stepN` world. Concretely, `Encoding.lean` now also exposes
> `bootstrap_cfg2` and `bootstrap_multistep`: 69 micro-steps from
> `Cfg2.blank` reach `Cfg.toSide (bigfootEnc Dyn.init)`, in either the
> `stepN2` or `Multistep` shape. The Bigfoot `Reduction.sim` proof can
> now be done in the busycoq-style tactical world instead of the
> ℤ-indexed tape — same recipe as BB33_494. Also renamed Multistep.lean's
> `stepN_add` to `stepN2_add` to avoid collision with `Reduction.lean`'s
> `BB.stepN_add` (which is for ℤ-tape `stepN`).
>
> **Session F (2026-05-26 evening, structure-finding pivot)**: Pivoted
> from "chase sim" to "make the Collatz-class framing precise." Added:
>
> * `lean/Collatz/Bigfoot/Classification.lean` (NEW, sorry-free) — proves
>   Ligocki's `Dyn.step` is a **3-dimensional generalized Collatz
>   function** (residue-affine on `b mod 6`, ℕ³ → Option ℕ³). Headline
>   theorem `Dyn.step_eq_bigfootRule`. Companion `Dyn.step_eq_none_iff`
>   shows the only halt branch is `(b mod 6 = 2 ∧ a = 0)`. Final
>   theorem `BigfootHypothesisArith_iff` reformulates Bigfoot's
>   non-halt as a pure ℕ-arithmetic statement, no TM machinery. Docstring
>   ties to Conway 1972, Lagarias 1985, Aaronson 2020. **The artifact
>   that converts "Bigfoot looks Collatz-shaped" from vibes into a Lean
>   theorem.**
> * `IsDecrementFiring`, `no_consecutive_decrements`, and
>   `no_consecutive_decrements_orbit` in `V6KPos.lean` (sorry-free) —
>   formalize the empirical observation "no two immediately consecutive
>   decrement firings in the V6 orbit" as a Lean theorem, proved from
>   `InvB.p1_a3_b_ge_7`. Rules out `D D` patterns; the next strengthening
>   (`D ... D ... D` ruled out) would need the `b mod 12 → terminus`
>   structure and is left open. Real structural fact about the dynamics.
>
> **What this session deliberately did NOT do**: dive into `Reduction.sim`.
> After honest calibration with Trevor, we concluded: the math content of
> Bigfoot is open (k_pos), sim is mechanical follow-up with no math
> payoff, and the higher-value move was to crystallize the open content
> structurally before chasing it. `Classification.lean` + the
> no-consecutive-decrements theorem are the artifacts that survive even
> if Bigfoot never closes.

---

## 0. TL;DR

**What is Bigfoot.** A specific 3-state 3-symbol Turing machine. The
current #1 holdout of the BB(3,3) busy-beaver enumeration: nobody knows
whether it halts. Empirically it doesn't, out to enormous step counts,
but the non-halt proof has been open since Shawn Ligocki's reductions
in the early 2020s.

**Where we are.** We have a V6 (k, a, b, pat) closed-form recurrence
that matches Bigfoot's TM dynamics at the super-cycle level, verified
to 1B V6 super-cycles in Python. In Lean we have:

* `V6Rule.lean` — defines the V6 rule + a 4-clause invariant `Inv` and
  proves `V6.no_halt` (the V6 rule itself never returns `none`).
  **Sorry-free.**
* `V6KPos.lean` — defines a strengthened 11-clause invariant `InvB`
  (parity + b-bounds), proves `InvB` is preserved and orbit-wide, and
  proves a sorry-free reduction `k_pos_orbit_of` from two cascade
  obligations to the headline `k_pos_orbit`. The two cascade
  obligations are the **only sorries**:
  - `k_at_9_ge_2_orbit : ∀ n s, orbit n = some s → s.pat = P1 → s.a = 9 → 2 ≤ s.k`
  - `k_at_3_ge_2_orbit : ∀ n s, orbit n = some s → s.pat = P1 → s.a = 3 → 2 ≤ s.k`

**What's still needed to close Bigfoot.**
1. Close those two cascade obligations in Lean (this is "the" Bigfoot
   problem in V6 coords).
2. Formalize the V6 ↔ TM correspondence (`Bigfoot.bigfootReduction.sim`),
   so V6's `no_halt` + `k_pos_orbit` together imply the TM doesn't
   halt. Currently a separate sorry in `lean/Collatz/Bigfoot/Reduction.lean`.

**Why this is interesting even if we don't close it yet.** The 2
cascade obligations are precisely Shawn Ligocki's `InvariantA` in V6
coordinates, transformed by the bijection φ. They factor the open math
content sharply: any closure ≡ a non-halt proof for Bigfoot. The 11
sorry-free clauses + the sorry-free reduction encode the structural
content we've extracted, formally.

---

## 1. The Bigfoot machine

3 states (A, B, C), 3 symbols (0, 1, 2). Transition table (canonical):

```
       0        1        2
  A  1RB      2LA      1RA
  B  1LC      2RB      1LB
  C  ---      2LA      0RC     (--- = halt)
```

Halt condition: state C reading symbol 0. (Halt transitions to A or
unspecified — the `---` cell.)

From the all-blank tape, the machine runs for an extremely long time
(Shawn has it past 10^200+ TM steps with no halt). The current
status: empirically infinite, mathematically unproven.

**Why this matters.** Bigfoot is one of a small number of remaining
holdouts in the BB(3,3) enumeration. Closing it (either way) advances
the formal verification of BB(3,3) = whatever-the-known-champion's
running time is.

**Bigfoot is sometimes called something else** in older BB literature
(Shawn's papers call it by its TM definition; the "Bigfoot" name is
borrowed from the project naming convention here). It's the same
machine.

---

## 2. The tape structure (super-cycle boundary form)

After a brief bootstrap, Bigfoot's tape settles into a recurring shape.
The tape, written with the head's neighborhood made explicit, has the
form

```
... 00 00 (1 2)^k 1^a 2^b TAIL ...
```

with `k`, `a`, `b` non-negative integers and `TAIL` one of two strings.

* **P1 pattern**: `TAIL = "1 2"`, head left of the right edge.
* **P2 pattern**: `TAIL = ε`, head inside the `2^b` block.

The TM's state and head position at the super-cycle boundary are
determined by the pattern. Specifically:

* P1 = "head looking left at the `1` boundary, state A or B in canonical
  position".
* P2 = "head sweeping right through `2^b`, state about to break out".

(For the exact pattern definitions, see `tools/sandbox/bigfoot_v5_tape_inspect.py`
where the RLE parse is implemented.)

Initial state of the **V6 recurrence** (matching cycle 5 of the literal
TM, the first stable P1 boundary): `⟨k=2, a=1, b=5, pat=P1⟩`.

---

## 3. The V6 9-rule recurrence

A single V6 "super-cycle" advances the tape through some bounded
number of TM micro-steps and returns a new boundary configuration.
There are nine rules:

```
P2(k, a, b)  →  P1(k, a-4, b+4)                       [P2→P1]

P1 with a even:
    a ≥ 4:    S        P1(k,   a-3,  b+5)
    a = 2:    W        P1(k,   b+4,  0)
    a = 0:    [none — would-be halt; ruled out by Inv]

P1 with a odd:
    a ≥ 11:   B        P1(k,   a-9,  b+11)
    a = 9:    B-coll   P1(k-1, 1,    b+12)
    a = 7:    Q-W      P1(k+1, b+7,  0)
    a = 5:    Q-same   P2(k,   b+7,  2)
    a = 3:    D-W      P1(k-1, b+7,  0)
    a = 1:    Q-kpp    P2(k+1, b,    3)
```

The rule lives at `tools/sandbox/bigfoot_v6_pure_rule.py` and at
`lean/Collatz/Bigfoot/V6Rule.lean`. **It is verified against the literal
TM at 996 cycles** (via `bigfoot_v5_stress.py`, which in turn is verified
against `BigfootV1` at 10k+ cycles) and was pushed to **1,000,000,000
super-cycles in ~167 seconds** with zero halts and no anomalies.

### Per-rule structural notes

* **S** (stretch). The dominant rule — most super-cycles are S firings.
  Reduces `a` by 3, grows `b` by 5. Doesn't touch `k`.
* **B** (big). Like S but at higher a, with `Δa = -9, Δb = +11`.
* **W** (wrap). Fires at a=2; the `2^b` block "wraps around" past the
  prefix, producing a new big `a`-block of size `b+4`.
* **Q-W** (quasi-wrap). Like W but at odd a=7, with `k` *incremented*
  (one extra (1 2) prefix block gained).
* **Q-kpp** (quasi-kpp). At a=1. Output is in P2 with k incremented.
  This is the increment-of-k partner of B-coll.
* **Q-same** (quasi-same-k). At a=5, k unchanged, output P2.
* **B-coll** (big collision). At a=9, k *decremented*. The output a=1
  forces a Q-kpp on the very next step, recovering the k.
* **D-W** (delayed wrap). At a=3, k decremented. The output a is *large*
  (b+7), so the trajectory enters an S/B chain before any rule that
  touches k again. Recovery is delayed (and is the harder of the two
  decrement rules).
* **P2→P1** (close-out). Always fires at P2 boundaries. Drops a by 4,
  grows b by 4, returns to P1.

### Δk per rule

```
P2→P1:  0       S:       0       W:       0
B:      0       B-coll: -1       Q-W:    +1
Q-same: 0       D-W:    -1       Q-kpp:  +1
```

Bigfoot's open question, **in V6 coords**, is whether `k` ever drops
below 1 over the orbit. Empirically `k ∈ [2, 16]` over 100M cycles;
proving this is exactly the open content.

---

## 4. The V6 ↔ Shawn (a, b, c) bijection

Shawn Ligocki has a parallel reduction of Bigfoot into a 6-rule
recurrence on `(a, b, c) ∈ ℕ³`. His system (`Dyn`) is implemented in
`lean/Collatz/Bigfoot/Dynamics.lean` and in
`tools/sandbox/bigfoot_shawn_dyn.py`. His open invariant `InvariantA`
(in `lean/Collatz/Bigfoot/InvariantSketch.lean`) is what would close
Bigfoot in his coords.

**The bijection** (derived empirically, then checked symbolically):

```
φ: Shawn (a_s, b_s, c_s)  ↦  V6 (a_s, 2·b_s − 1, 2·c_s + 1, P1)

i.e. V6's k = Shawn's a; V6's a = 2·b_s − 1; V6's b = 2·c_s + 1.
```

The inverse (at invertible-V6 states with V6's a, b both odd, pat=P1):

```
φ⁻¹: V6 (k, a_v, b_v, P1)  ↦  Shawn (k, (a_v + 1)/2, (b_v − 1)/2)
```

Verified at the first 10 Shawn boundaries, which appear in V6 at steps
0, 2, 4, 6, 9, 14, 19, 26, 36, 50 (`bigfoot_bijection_check.py`).

**Consequence.** V6's `k_pos` ≡ Shawn's `InvariantA` (modulo the
correspondence formalization). They are the same theorem in different
coordinate systems. Shawn's coordinate system has *multiplicative* b
growth (×4/3 per step), making backward case analysis intractable. V6's
has *additive* b growth (Δb ≤ 12), which is what motivated the V6 work
— there's hope for a finite cascade in V6 that's hopeless in Shawn's.
The dig in §9 below shows that hope is fading but not dead.

---

## 5. The halt condition and what's needed for TM no-halt

V6's `step` function returns `none` exactly when `(pat=P1, a=0)`.
That's the V6 halt precursor. Other rules' outputs in ℕ have natural
subtraction (`s.k - 1` may be 0) but don't break the rule's well-defined
forward progress — `step` returns `some _`.

`V6.no_halt` (proved in `V6Rule.lean`): `∀ n, V6.orbit n ≠ none`.

**This is NOT sufficient for the TM not halting.** The reason is the
V6 ↔ TM correspondence breaks when `k = 0`:

* V6's `(12)^k` prefix vanishes at k=0.
* At that point, V6's rule semantics no longer match the TM's tape
  evolution — the TM has different boundary behavior with no prefix.
* So `k_pos: 1 ≤ s.k` must hold along the entire V6 orbit for the
  V6→TM correspondence to remain valid.

Putting it together, what's needed:

1. **V6.no_halt** (✓ done).
2. **V6.k_pos_orbit**: `∀ n s, V6.orbit n = some s → 1 ≤ s.k` (open).
3. **Reduction.sim**: V6 super-cycle ↔ TM micro-step correspondence
   (sorry'd in `Reduction.lean`, parked for now — weeks of mechanical
   Lean work, no new math).

Closing (2) and (3) closes Bigfoot.

---

## 6. The structural invariant `InvB` (11 clauses, sorry-free)

`V6KPos.lean` carries a strengthened invariant past `V6Rule.lean`'s
4-clause `Inv`. All 11 clauses are proven preserved, sorry-free.

```lean
structure InvB (s : State) : Prop where
  -- the 4 from V6Rule.Inv
  p1_a_pos      : s.pat = P1 → 1 ≤ s.a
  p1_a1_b5      : s.pat = P1 → s.a = 1 → 5 ≤ s.b
  p2_a_5        : s.pat = P2 → 5 ≤ s.a
  p2_a5_b3      : s.pat = P2 → s.a = 5 → s.b = 3
  -- structural b-bounds (P2 has very tight b: only {2, 3})
  p2_b_ge_2     : s.pat = P2 → 2 ≤ s.b
  p2_b_le_3     : s.pat = P2 → s.b ≤ 3
  p2_b2_a_ge_7  : s.pat = P2 → s.b = 2 → 7 ≤ s.a
  p1_a3_b_ge_7  : s.pat = P1 → s.a = 3 → 7 ≤ s.b
  p1_a2_b_ge_7  : s.pat = P1 → s.a = 2 → 7 ≤ s.b
  -- parity invariant
  parity_ab     : (s.a + s.b) % 2 = 0
  -- supports the p1_a3_b_ge_7 strengthening
  p1_a6_b_ge_6  : s.pat = P1 → s.a = 6 → 6 ≤ s.b
```

### Why each new clause holds, briefly

* **p2_b_ge_2, p2_b_le_3.** The only rules with pat=P2 output are Q-same
  (literal b=2) and Q-kpp (literal b=3). So P2 b ∈ {2, 3}.
* **p2_b2_a_ge_7.** If P2 with b=2, the rule that produced it must be
  Q-same (Q-kpp gives b=3). Q-same outputs (k, b_in + 7, 2, P2) with
  `a_out = b_in + 7 ≥ 7` (b_in ≥ 0 in ℕ).
* **p1_a3_b_ge_5** (original) / **p1_a3_b_ge_7** (strengthened). D-W
  fires at (P1, 3, b). Sources: S from (P1, 6, b−5), and P2→P1 from
  (P2, 7, b_p2). The strengthening to ≥ 7 uses parity (forces P2(7) to
  have b_p2 = 3 odd, ruling out the b_p2 = 2 case) and `p1_a6_b_ge_6`
  (rules out the source (P1, 6, 0)).
* **p1_a2_b_ge_7.** W fires at (P1, 2, b). Sources: B from (P1, 11)
  giving b ≥ 11, and P2→P1 from (P2, 6, 3) giving b = 7.
* **parity_ab.** Every rule's Δ(a + b) is in {0, 2, 4}. Initial state
  has (a + b) = 6 (even). Verified empirically over 100M cycles with
  zero violations. This is the SINGLE BIGGEST STRUCTURAL FACT we've
  found about V6.
* **p1_a6_b_ge_6.** Sources of (P1, 6, b): B from (P1, 15) gives b ≥ 12;
  W from (P1, 2) with `p1_a2_b_ge_7` gives b ≥ 11; P2→P1 from (P2, 10)
  with parity + p2_b_le_3 forces b_p2 = 2 hence output b = 6. S source
  vacuous (needs even input a, but a=9 is odd).

### What InvB buys (and doesn't)

It buys: a tight structural skeleton of where the orbit lives in
`(a, b, pat)` space. In particular:

* At (P1, 3) and (P1, 9), b is **odd** (from parity).
* At (P2), b ∈ {2, 3}.
* `(P1, 3, 5)`, `(P1, 6, 0)`, `(P2, 7, 2)`, `(P1, 1, even b)`, and many
  other small "bad" states are RULED OUT.

It doesn't buy: any direct bound on `k`. That's what the cascade
obligations are for.

---

## 7. The factored open content (2 sorries)

`V6KPos.lean` ends with:

```lean
/-- Sorry-free factoring lemma. -/
theorem k_pos_orbit_of (cascade : KPosCascade) :
    ∀ n s, orbit n = some s → 1 ≤ s.k := by
  obtain ⟨h9, h3⟩ := cascade
  -- induction on n, case-split on rules, use h9 / h3 at B-coll / D-W.
  ...

abbrev KPosCascade : Prop :=
  (∀ n s, orbit n = some s → s.pat = P1 → s.a = 9 → 2 ≤ s.k) ∧
  (∀ n s, orbit n = some s → s.pat = P1 → s.a = 3 → 2 ≤ s.k)

theorem k_at_9_ge_2_orbit : ... := by sorry   -- OPEN
theorem k_at_3_ge_2_orbit : ... := by sorry   -- OPEN

theorem k_pos_orbit : ∀ n s, orbit n = some s → 1 ≤ s.k :=
  k_pos_orbit_of ⟨k_at_9_ge_2_orbit, k_at_3_ge_2_orbit⟩
```

So the open content of Bigfoot, in V6 coords, is **exactly** the two
named theorems above. Through φ, they are equivalent to Shawn's
`InvariantA` from `InvariantSketch.lean`. Closing either closes
Bigfoot's k_pos question (and combined with `Reduction.sim`, closes
Bigfoot non-halt).

---

## 8. The deep structural fact: b mod 12 → post-D-W chain terminus

This is the single most useful observation we've made about V6's
trajectory structure.

**D-W output is `(k-1, b+7, 0, P1)`** with input b ≥ 7 odd (by parity
and `p1_a3_b_ge_7`). So the output a is `b + 7 ≥ 14`, even.

After D-W, the trajectory enters an **S/B alternation chain** (S fires
at even a, B at odd a ≥ 11), with k unchanged through the chain.
Each (S, B) pair reduces a by 12. The chain terminates when a drops to
a value that's not S- or B-applicable, i.e., a ∈ {1, 2, 3, 5, 7, 9}.

The terminus is determined entirely by `(b + 7) mod 12`, equivalently
by `b mod 12`:

| D-W input b mod 12 | Output a mod 12 | Terminus a | Terminus rule | k-effect |
|---|---|---|---|---|
| 1  | 8  | 5  | Q-same  | k unchanged |
| 3  | 10 | 7  | Q-W     | **k recovers (+1)** |
| 5  | 0  | 9  | B-coll  | TRANSIENT k=k-2, then Q-kpp → k-1 |
| 7  | 2  | 2  | W       | k unchanged |
| 9  | 4  | 1  | Q-kpp   | **k recovers (+1)** |
| 11 | 6  | 3  | D-W     | **SUSTAINED k=k-2** (second D-W!) |

(Only odd residues since b is odd by parity.)

**Dangerous classes**: `b mod 12 ∈ {5, 11}`.

* `b mod 12 = 5`: the chain ends in B-coll, dropping k to k-2 for ONE
  step before Q-kpp restores to k-1. For `k_pos ≥ 1`, we need
  **D-W input k ≥ 3** at firings with b mod 12 = 5.
* `b mod 12 = 11`: the chain ends in another D-W, sustaining k=k-2 and
  threatening further drops.

**Empirically (100M cycles):**

* D-W firings: 7 total, b values `{7, 69, 773, 1851, 18555, 2469445, 58469179}`.
* b mod 12 distribution: `{1, 3, 5, 7, 9}` — class 5 has ONE hit (b=773
  with k=5), class 11 has ZERO hits.
* The b=773 case worked out because k=5 at that firing, comfortably ≥ 3.
* B-coll firings: 8 total, similar sparse distribution; min input k = 3.

**Honest takeaway.** If we could prove **`b mod 12 ≠ 11` at all
reachable (P1, 3, b)**, we'd rule out sustained double decrements
entirely. The transient `b mod 12 = 5` case would still require
`k ≥ 3` at those firings (empirically true). We'd then need to prove
`k_at_3 ≥ 3` (stronger than `≥ 2`), which has its own cascade issues —
B-coll outputs at k=k_in - 1 = 2, and (P1, 9) firings with k=2 are
allowed (if (P1, 9) were reachable with k=2), pushing the cascade up
one more level.

---

## 9. The cascade: why it doesn't close in finite Lean clauses

To prove `k_at_9_ge_2_orbit` by induction, we need preservation of
`k ≥ 2` at every reachable (P1, 9) state. The sources of (P1, 9) are:

* S from (P1, 12, b−5). Same k, so need k_at_12 ≥ 2.
* P2→P1 from (P2, 13, b−4). With parity + p2_b_ge_2 + p2_b_le_3, b_p2 = 3
  → output b = 7. So source is (P2, 13, 3). Empirically (P2, 13, 3) is
  unreachable (its sources are all blocked by similar invariant chains).
* W, Q-W, D-W, B sources: all blocked by parity + existing b-bounds.

So effectively `k_at_9 ≥ 2` ⇐ `k_at_12 ≥ 2`. Cascade upward.

`k_at_12 ≥ 2` ⇐ `k_at_21 ≥ 2` (only source is B from (P1, 21)).
`k_at_21 ≥ 2` ⇐ `k_at_24 ≥ 2` ∧ `k_at_p2_a25 ≥ 2`.
`k_at_24 ≥ 2` ⇐ `k_at_33 ≥ 2` ∧ ... (B source); plus side sources via
W (gated by p1_a2_b_ge_X), Q-W, D-W, P2→P1.

The chain `(P1, 9) ← S ← (P1, 12) ← B ← (P1, 21) ← S ← (P1, 24) ← B ← (P1, 33) ← S ← ...`
goes **infinitely upward in a**. Each level needs a fresh `k_at_X_ge_2`
clause.

At higher a, "side entries" from W/Q-W/D-W can introduce new branches
(producers like (P1, 2, large b) or (P1, 7, large b) or (P1, 3, large b)),
each of which would need its own k bound. Some are vacuous via parity,
but in general the side-entry tree is also infinite.

**Bottom line:** there's no terminating finite cascade. To close
`k_at_9_ge_2_orbit` you need a non-local argument:

* A Lyapunov function `phi(s)` whose evolution gives `k ≥ 1`.
* Or a phase-/trajectory-aware invariant.
* Or a global argument routing through Shawn's coordinate system
  via the bijection.

---

## 10. Empirical data (100M V6 cycles, 1B in earlier runs)

* **k_min = 2** (achieved at initial state and right after B-coll firings).
* **k_max = 16** (over 100M cycles; was higher in the 1B run — k drifts
  upward overall).
* **Max consecutive decrements (without intervening Q-W or Q-kpp): 2.**
  After 2 decrements there's always at least one increment before a 3rd.
* **D-W and B-coll firings are very sparse** — 7 and 8 respectively in
  100M cycles. Rule histogram is dominated by S (~50%), B (~50%), W is
  rare, the "interesting" rules are exponentially rare.
* **(P2, a)** is empty for most small a (e.g., (P2, 10), (P2, 13)). Only
  observed P2 states with a ≤ 30: (P2, 5, 3), (P2, 7, 3), (P2, 28, 2).
  This is one of the strongest empirical facts and suggests P2 visits
  are tightly constrained.

For tools:

* `tools/sandbox/bigfoot_v6_kpos_analysis.py` — orbit analyzer.
* `tools/sandbox/bigfoot_v6_reach_map.py` — residue + k_min map per
  (pat, a).
* `tools/sandbox/bigfoot_bijection_check.py` — V6 ↔ Shawn empirical
  verifier.

---

## 11. The Lean files in detail

### `lean/Collatz/Bigfoot/V6Rule.lean` (369 lines, sorry-free)

* `Pat`, `State`, `step`, `initial`, `orbit` — the V6 definitions.
* `Inv` — the 4-clause invariant (just `a, b, pat` constraints — no
  parity, no k).
* `step_X` per-rule unfolding lemmas (one per rule). Non-private so
  `V6KPos.lean` can reuse.
* `Inv_initial`, `step_preserves_Inv`, `orbit_Inv`.
* `step_ne_none_of_Inv` — from `Inv`, `step` never returns `none`.
* `V6.no_halt` — the headline.

### `lean/Collatz/Bigfoot/V6KPos.lean` (519 lines, 2 sorries)

* `InvB` — the strengthened 11-clause invariant.
* `InvB.toInv` — forget the strengthening, recover `Inv`.
* `InvB_initial`, `step_preserves_InvB`, `orbit_InvB` — sorry-free.
* `KPosCascade` — abbreviation for the conjunction of the two cascade
  obligations.
* `k_pos_orbit_of` — sorry-free reduction.
* `k_at_9_ge_2_orbit`, `k_at_3_ge_2_orbit` — the 2 sorries.
* `k_pos_orbit` — application of the reduction.

### `lean/Collatz/Bigfoot/InvariantSketch.lean` (experimental, sorry'd)

Shawn-coords version of the same open question. Contains
`Collatz.Bigfoot.invariantA_sorry`. Useful for cross-referencing with
the V6KPos sorries via the bijection φ.

### `lean/Collatz/Bigfoot/Reduction.lean` (sorry'd)

The V6 ↔ TM correspondence (well, technically the Shawn-coords ↔ TM
correspondence, set up so that we can swap in V6 if needed). Has
`Bigfoot.bigfootReduction.sim` as a sorry. **Independent of k_pos;
needs to be done for Bigfoot to close even if k_pos is proved.**

### Other Lean files (no sorry contributions here)

`Machine.lean`, `Dynamics.lean`, `Hypothesis.lean`, `Encoding.lean` —
foundation, all clean.

---

## 12. Build and run commands

```bash
# Default Lean build (3 pre-existing sorries: Tao, Korec, Bigfoot.sim).
cd ~/src/collatz-cryptid/lean && lake build

# Explicit V6 build (adds 2 cascade sorries to the warning count).
cd ~/src/collatz-cryptid/lean && lake build Collatz.Bigfoot.V6KPos

# Empirical: 100M-cycle k/b/parity analysis.
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_v6_kpos_analysis.py 100000000

# Empirical: reachable (pat, a, b mod 12) map.
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_v6_reach_map.py 100000000 30

# Empirical: V6 ↔ Shawn bijection check (sparse boundary samples).
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_bijection_check.py

# Pure V6 rule, 1B cycles (~3 minutes wallclock).
sandbox ~/src/collatz-cryptid/tools/sandbox/bigfoot_v6_pure_rule.py
```

---

## 13. Concrete next-swing options

In rough order of "promising and tractable":

### (b) Pivot to V6 ↔ TM correspondence (`Reduction.sim`)

* **Status**: independent of k_pos; required for Bigfoot closure regardless.
* **Approach**: formalize the V6 super-cycle as a composition of TM
  micro-steps. The 9 V6 rules each correspond to specific TM rule
  sequences; each can be verified by Lean's `decide` on small tape
  projections.
* **Estimated effort**: weeks of mechanical Lean. No new math.
* **Why first**: even if k_pos remains open, having `Reduction.sim`
  proved means we ONLY need k_pos to close Bigfoot. Right now we need
  k_pos AND sim, so neither is sufficient alone.

### (c) Lyapunov function search

The natural ansatz: `phi(s) = 2·s.k + f(s.a mod 12, s.b mod 12, s.pat)`.
We want Δphi ≥ 0 along every rule, so phi is non-decreasing, and we
want phi → ∞ to imply k → ∞ (or at least k ≥ 1).

* The b mod 12 → terminus map is a strong hint: f should "anticipate"
  the cost of an upcoming decrement.
* Linear-in-(a, b) doesn't work because W/Q-W/D-W reset b to 0
  (Δb = -current b, which isn't linear).
* Worth trying: piecewise-linear f indexed by (s.a mod 12, s.pat).
* Risk: even if a clean Lyapunov exists for V6 specifically, Shawn's
  multiplicative coords have been searched for years without one.

### (d) Trajectory-aware invariant

Statement: "Between any two consecutive D-W or B-coll firings on the
orbit, there is at least one Q-W or Q-kpp firing."

* Empirically TRUE (max consecutive decrements = 2, and after 2 there's
  always a recovery before a 3rd).
* Would require formalizing a "look-ahead" or "look-behind" predicate
  on orbit indices. Mathlib has some support for this (via finite-trace
  predicates) but not natively in our framework.
* Hard but maybe doable; if so, k_pos follows by simple counting.

### (a) Keep chipping the cascade with state-specific clauses

* Each new clause (`p1_a9_b_ne_5`, `p1_a12_b_ne_8`, etc.) is mechanical
  to prove (~30-50 lines) given parity + existing clauses.
* Doesn't close sorries on its own, but tightens the danger surface
  one inch at a time.
* Use as a fallback when other approaches stall.

### (e) External structural insight

Bigfoot has been studied for years by the BB community. There may be
existing results (Shawn's notes, the BB busy-beaver mailing list,
Pavel Kropitz's archive) that give a phase structure or a known
invariant we don't have here. Worth a literature scan if other
approaches stall.

(**Don't ping Shawn directly** — see Trevor's memory note `feedback_no_shawn_pings.md`.)

---

## 14. Files inventory

### Lean
* `lean/Collatz/Bigfoot/V6Rule.lean` — V6 + no_halt (sorry-free).
* `lean/Collatz/Bigfoot/V6KPos.lean` — InvB + k_pos factoring (2 sorries).
* `lean/Collatz/Bigfoot/InvariantSketch.lean` — Shawn-coords parallel (sorry'd).
* `lean/Collatz/Bigfoot/Reduction.lean` — TM correspondence (sorry'd at `sim`).
* `lean/Collatz/Bigfoot/Dynamics.lean` — Shawn's Dyn rule.
* `lean/Collatz/Bigfoot/Encoding.lean` — TM tape encoding.
* `lean/Collatz/Bigfoot/Machine.lean`, `Hypothesis.lean` — foundation.

### Python (sandbox)
* `tools/sandbox/bigfoot_v1_literal.py` … `bigfoot_v5_*.py` — the
  rewrite chain that derived V6.
* `tools/sandbox/bigfoot_v6_pure_rule.py` — V6 iterator (1B-cycle ready).
* `tools/sandbox/bigfoot_shawn_dyn.py` — Shawn's 6-rule Dyn simulator.
* `tools/sandbox/bigfoot_compare_v6_shawn.py` — side-by-side TM comparison.
* `tools/sandbox/bigfoot_bijection_check.py` — empirical bijection verifier.
* `tools/sandbox/bigfoot_v6_kpos_analysis.py` — orbit analysis + parity check.
* `tools/sandbox/bigfoot_v6_reach_map.py` — residue + k_min map per (pat, a).

### Notes (markdown)
* `notes/16-bigfoot-rewrite-series.md` — v1→v4 decompilation.
* `notes/17-bigfoot-v5-recurrence.md` — v5/v6, 1B-cycle empirical no-halt.
* `notes/18-v6-k-pos-attempt.md` — by-hand cascade analysis.

---

## 15. Conventions used

* **k, a, b**: V6 super-cycle state components. k = number of (1 2)
  prefix blocks; a = length of 1-block at the head's boundary;
  b = length of 2-block at the head's boundary.
* **a_s, b_s, c_s**: Shawn-coords analog. Related to (k, a, b) by φ.
* **P1 / P2**: super-cycle pattern (`TAIL = 1 2` / `TAIL = ε`).
* **Parity**: `(a + b) % 2 = 0` at every reachable state. Trevor-confirmed
  empirically and Lean-proved (parity_ab clause).
* **Bigfoot vs. Holdout 153/397/531**: this file is only about Bigfoot
  (BB(3,3) holdout #1). The others are different cryptids tracked in
  `HANDOFF.md` — 153 was refuted (4-counter conjecture), 397 is
  shape-explosive PDA, 531 is shape-explosive without saturation.

---

## 16. Behavioral notes for Claude (if you're a fresh session)

* **Use `trash` not `rm`** for file deletions (hook-enforced).
* **Use `sandbox` not bare `python3`** for sandbox Python scripts.
* **Use `lake build Collatz.Bigfoot.V6KPos`** for incremental builds.
* **Don't ping Shawn Ligocki** — Trevor is protective of the
  relationship; he'll initiate if appropriate.
* **`bin/o <path>.lean`** opens Lean files in VS Code at the correct
  workspace root (Lake-aware).
* **Lean probe files**: use the `Write` tool + `lake env lean <path>`,
  never `cat > foo.lean <<'EOF'` heredocs.
* **Mathlib version**: follows the `rev` pinned in `lakefile.toml`, which
  tracks the toolchain in `lean-toolchain`. Do not bump without checking —
  many proofs depend on subtle naming.

---

## 17. Honest assessment of where we are

Bigfoot's k_pos open question, in V6 coords, is *factored* in Lean
into two named theorems plus a sorry-free reduction. This is real
formal progress: it converts an English-language paragraph in
`notes/18` into a Lean type signature that can be the target of a
future proof attempt by anyone.

That said: the cascade doesn't close finitely. The 11 InvB clauses we
have rule out the SMALL bad cases (state-by-state unreachability of
specific (a, b) configurations), but the empirical k-trajectory's
"k stays bounded ≥ 2" fact requires structural reasoning we haven't
found. Likely paths to actual closure:

* Find a Lyapunov function (~25% odds).
* Find a trajectory-aware invariant (~15%).
* Get lucky with external BB literature (~10%).
* Sustained chipping with state-specific clauses (~5% — the cascade is
  infinite, so this only closes if the chain miraculously terminates
  at some large a we haven't reached).

The `Reduction.sim` work is **orthogonal and required** regardless.
That's where I'd start next: it's mechanical (no open math), it's
necessary for any Bigfoot closure, and finishing it means k_pos is the
only remaining piece. Right now both are open.

🦶
