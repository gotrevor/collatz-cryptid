# 27 - The map of Erdős's seam 🗺️

**Date**: 2026-05-28 (evening, continuation). **Mode**: synthesis + one dynamic
Lean swing. **Frame**: Trevor asked "what's itching" and named the real itch -
*are we being too disciplined to find the actual bridge?* This note is the answer
we can stand behind: a complete formal **map** of a famous open problem's seam,
built without crossing it and without pretending to.

This is methodology as much as math. Read it as a case study in using Lean + an AI
partner as a **depth instrument** - a way to *see the shape* of hard territory.

---

## 1. The territory: "2 ≠ 3" has three faces

Multiplicative independence of 2 and 3 (`log₂ 3 ∉ ℚ`) wears three inequivalent
faces, and conflating them is a category error (notes/26):

| face | kind of question | headline conjecture |
|------|------------------|---------------------|
| **magnitude / Diophantine** | how close can `2^L` get to `3^n`? | Collatz, Pillai (`\|2^L − 3^n\|`) |
| **digit / automata** | what do the base-3 digits of `2^n` look like? | **Erdős** (a `2` always appears, `n>8`) |
| **dynamical / ergodic** | rigidity of the `×2, ×3` action | Furstenberg |

These are not mutually reducible. The honest, provable relationships live at the
**interfaces between faces**, never face-to-face. Erdős is the digit face, and it
is the one we mapped completely tonight.

## 2. The seam: low digits provable, high digits open

Erdős splits at the lowest base-3 digit:

- **odd `n`**: `2^n ≡ 2 (mod 3)`, so the low digit is already `2`. **Done.**
  (`Partial.erdos_odd`.)
- **even `n`**: `2^n ≡ 1 (mod 3)`, low digit `1`; a `2` must appear among the
  **high** digits. *This is the entire open content.*

So Erdős(even) is a question about **high digits of a deterministic-but-complex
string**: does that string ever, past `n=8`, avoid the digit `2` entirely? That is
a coverage / avoidance question - the Tao signature, **density-1-easy,
measure-0-hard**. Almost no `2^n` is digit-2-free; proving *none* are (past 8) is
the wall.

## 3. Both walls are now formal

Tonight we pinned **both sides** of the seam in Lean.

### Low wall - perfectly rigid (proved, general `k`)
`Lifting.orderOf_two_mod_three_pow` : `orderOf (2 : ZMod (3^k)) = 2·3^{k-1}` for all
`k ≥ 1`. **2 is a primitive root mod every `3^k`**, so over one period `2^n mod 3^k`
hits *every* unit exactly once - the low `k` digits are perfectly equidistributed.
Proved from an elementary LTE witness `v₃(2^{2·3^j} − 1) = j+1` (binomial induction,
no `multiplicity` API). This **retired a `k ≤ 4` machine-checked cap** - a real
fudge removed.

### High wall - pseudorandom (proved)
`Sturmian.leadingDigit_mem` + the Sturmian-complexity argument: the leading base-3
digit of `2^n` is a Sturmian sequence (irrational rotation by `{n log₃ 2}`), hence
**not automatic** (Cobham). High digits are not finite-state.

### The canyon between them is Erdős
Low is deterministic-and-uniform; high is pseudorandom; the question of whether a
`2` always appears lives in the gap. We proved the walls; the canyon stays open *by
necessity*.

## 4. The bridge object: the carry process

A base-3 digit of `2^n` equals `2` **iff** a carry-state `(1,0)` or `(2,1)` of the
doubling CA occurs (`Carry.doubleDigit_fst_eq_two`). A carry fires exactly when the
local sum reaches the base (`2d+c ≥ 3`) - a *magnitude* threshold that is a
*digit-level* event. The carry is the literal mechanism that transports low-digit
structure up into the high digits. It is **the only bridge across the seam.**

We built the bridge as a Lean object, in three layers:

1. **Erdős ⟺ carry-positivity** (`Carry.erdos_iff_carryPositivity`). A genuine
   equivalence (was a vacuous placeholder; now a theorem, axiom-clean). Erdős *is*
   "the doubling carry field is never 2-sparse past `n=8`."

2. **Kummer conservation** `s(2L) + 2·C(L) = 2·s(L)` and its telescoped closed form
   **`s₃(2^n) + 2·Σ_{j<n} 2^{n-1-j} C_j = 2^n`** (`CarryProcess`). Numerics:
   the digit sum `s₃(2^n)` is tiny (`n=11 → 10`) while the carry-weighted sum
   `W(n) ≈ 2^{n-1}`. So `2^n` is *overwhelmingly* carry-made; the digit sum is a
   vanishing correction.

3. **The avalanche** (`CarryProcess.doubleAux_avalanche`, **no axioms**):
   `1^k 0 ↦ 0^k 1` under an incoming carry - a carry races through a block of `1`s
   flipping them to `0`, until a `0` absorbs it. The odometer increment
   `…0111 + 1 = …1000`, here as base-3 doubling's carry sub-process.

## 5. The honest verdict (the discipline, examined)

Here is the thing the map makes undeniable, and it answers Trevor's itch.

**Layers 1 and 2 are kinematic.** The conservation law holds for *every* list `L`,
not just `iterCA n`. The equivalence is a re-coordinatization. They are true, clean,
axiom-free - and they say nothing specific about `2^n` that could *cross* the seam.
They are bookkeeping for a relationship, not a transmission of information between
the faces.

**Layer 3 is dynamic** - the avalanche is about how a carry *moves*. And this is
exactly where the difficulty re-localizes, not where it dissolves. Carries provably
reach arbitrarily high (trivially: `2^n` has `~0.63n` base-3 digits, the top moves
up, and a new top digit is born only from a carry out of the old top). The open
content is the **avalanche distribution**: do the carries ever, across the whole
finite string, dodge *both* 2-making patterns `(1,0)` and `(2,1)`? That is a large
deviation fact about a deterministic avalanche, and the carry process re-expresses
it faithfully **without reducing it.**

So: **was the discipline ("refuse the grand unification, build interfaces, slap an
honesty rail on each") wisdom, or were we too disciplined to find the bridge?**

The map's verdict: the discipline was *correct*, and that is precisely why it
couldn't find a bridge that crosses. Every interface we can *prove* is kinematic -
true-for-all-inputs - because anything that genuinely used "2 vs 3" specifically
would *be* a solution to the open problem. The bridge we keep not-finding is not
hiding behind insufficient cleverness; **a crossing bridge would be a proof of
Erdős.** The interfaces are real and they are kinematic *by the structure of the
problem*, not by our timidity.

What the discipline cost us is nothing. What it bought us is this map - and the map
is itself the deliverable. We now have, in Lean, 0 sorries, axiom-clean except where
honestly axiomatized:

- both walls of the seam (low: primitive-root rigidity, general `k`; high:
  Sturmian non-automaticity),
- the bridge object across it (carry process: equivalence + conservation + closed
  identity + avalanche),
- the open content named precisely (the avalanche-coverage / Furstenberg-stiffness
  statement), and
- a fudge retired (`k ≤ 4` cap gone).

That is a **complete formal cartography of a famous open problem's hardness** - the
shape of the canyon traced from both rims and the one bridge mechanism characterized
- produced without solving it and without overclaiming. That is what the depth
instrument is *for*.

## 6. Where a real crossing would have to come from

If a bridge exists, the map says where: not in more kinematic identities, but in a
**dynamical theorem about the avalanche distribution** that is *specific to the seed
`[1]`* (i.e. to `2^n`, not all `L`). The candidate shape: a statement that the
carry avalanches of the `2^n` chain cannot collectively avoid the 2-making cells -
an ergodic / equidistribution input about *where* carries land, not merely *how many*
there are. That is the same content as Furstenberg `×2,×3` rigidity, projected to
the digit altitude. Which is to say: the bridge, if built, is Furstenberg. The map
closes the loop - the three faces meet only at the open problem itself.

---

*Status: `lake build Collatz.Erdos` clean, 0 sorries. New tonight:
`doubleAux_avalanche` (no axioms). This note is a candidate blog post - Trevor's
call. It pairs with `soul/unification-itch.md` and the AlphaMaster / AI-as-depth
thread.*
