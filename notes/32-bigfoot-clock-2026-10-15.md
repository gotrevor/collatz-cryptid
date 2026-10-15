# 32 - Bigfoot's parity clock, Bigfoot as a `Hydra`, and a census of shared engines

*2026-10-15, lane T1 of the cross-lane review (`tmp/context/crossreview.md` §5).  New
structural facts about open problems; nothing here settles Bigfoot or Antihydra.*

Tags: **Lean** = proved in this repo, axioms `propext, Classical.choice, Quot.sound` only, no
`native_decide`; **computed** = exact script with a control; **paper** = argued, not formalized.

## 1. The parity clock (Lean, 100%)

`Dyn` is Ligocki's `(a, b, c)` reduction (`lean/Collatz/Bigfoot/Dynamics.lean`).  Every branch
adds an odd constant to `8⌊b/6⌋ + c`, so `b' ≡ c + 1 (mod 2)`; the new `c` is `2` after an
even residue and `3` or `5` after an odd one, so `c' ≡ b (mod 2)`.

| Statement | Declaration (`lean/Collatz/Bigfoot/Clock.lean`) |
|---|---|
| two steps flip `b mod 2`, from **any** state | `Dyn.step_step_parity` |
| along the orbit, `b_{n+2} ≡ b_n + 1 (mod 2)` | `Dyn.parity_clock` |
| `b_n` odd iff `n ≡ 0, 1 (mod 4)` | `Dyn.orbit_b_mod_two` |
| `c_n = 2` at `n ≡ 0, 3`; `c_n ∈ {3, 5}` at `n ≡ 1, 2 (mod 4)` | `Dyn.orbit_c_phase` |

So `b mod 2` carries no information: all of the mixing is in `b mod 3`.  The counter `a` moves by
`{0, −1, +1}` at even residues and by `{+1, 0, 0}` at odd ones, so only phases 2 and 3 can
decrement.

## 2. Bigfoot is a `Hydra` in int-y1's schema (Lean, 100%)

In the coordinate `X = 4b + 3c` the `c`-dependence of the step cancels (`4/3 · 3c = 4c`), and
one step is `X ↦ 32⌊X/24⌋ + h[X mod 24]`, `a ↦ a + w[X mod 24]`.  The halt branch is exactly the
walk stepping to `−1`.

* `Dyn.hydraIterate_X`, `Dyn.hydraIterate_X_none`: one step in the `Hydra` schema.
* **`Dyn.nonhalt_iff_hydra`**: `(∀ n, orbit n ≠ none) ↔ Hydra 32 24 bigfootH bigfootW (10, 2)`.

`Hydra` and `hydraIterate` are transcribed verbatim from int-y1's `proofs/BBfLean/Cryptid.lean`
(opened; `~/src/reservoir/int-y1`), so Bigfoot now sits in the same schema as int-y1's 12 open
BBf props.  The slope is 4/3, the same as `hydra218 : Hydra 4 3 [1,2,3] [3,1,-1] (1,3)`.  Bigfoot's
modulus is 24 rather than 3 because of the parity clock and the 3-valued `c`.  **Not shown:** a
conjugacy between Bigfoot and #218.  "Same family" is all that is claimed.

## 3. The clocked block map (Lean, 100%; prior work)

From a phase-0 state (`b` odd, `c = 2`) with `a ≥ 2`, four steps send `(a, 162q + r, 2)` to
`(a + w₄[r], 512q + g₄[r], 2)`, with slope `(4/3)⁴ = 256/81` (**`Dyn.step4_block`**).  The engine is
a base-3 `×4/3` map read off `b mod 162`, i.e. off four base-3 digits plus the forced parity.

**Prior work.**  This is LegionMammal978's reduced map
`C(a, 81k + r) → C(a + Δa, 256k + s)` with `C(a, β) = A(a, 4β + 1, 2)` (`bigfoot-sim`, Oct 2023,
local clone `~/src/bb-deep-dive/bigfoot-sim/src/main.rs`, `TABLE`).
**`Dyn.step4_legion`** proves his 81-entry table verbatim, which cross-checks the repo's `Dyn`
transcription of Ligocki against an independent primary source.  His representation already
implies the clock (a `c = 2` state every 4th step), and it also implies the finer fact that
`b ≡ 1 (mod 4)` at phase 0.  So the *reading* "4-phase clock plus a base-3 engine" is folklore
in substance (~85%), even if nobody stated the 2-step parity lemma.  What is new here is the
proofs, the one-step `Hydra 32 24` form, and the drift identity below.

**Drift.**  `blockW_sum`: the block walk sums to `54` over the `81` residues, a mean of `+2/3`
per block, i.e. `+1/6` per step under the uniform (Haar) law on `b mod 162`.  This is the exact
form of "drift +1/6" (Lean).  On the actual orbit (computed): `a = 16601` after `10⁵` steps
(`0.166/step`), with zero clock violations and zero conflicts in fitting the block table from the
orbit.  Control: the same fit with a wrong slope (`256q` in place of `512q`) gives 24918
conflicts.

**Summary sentence**, stated exactly: Bigfoot is the counter walk of the `×256/81` base-3 block
map `b ↦ 512⌊b/162⌋ + g₄[b mod 162]` (four steps of a `×4/3` map whose parity is a 4-phase clock),
with walk mean `+1/6` per step.  Halting is the walk going negative (`nonhalt_iff_hydra`).

## 4. Census of shared engines (Lean, `lean/Collatz/Census.lean`)

Every map is written in int-y1's `Hydra` schema.  The two canonical floor engines are
`H(u) = ⌊3u/2⌋` (`hydraIterate 3 2 [0,1]`) and `K(u) = ⌊4u/3⌋` (`hydraIterate 4 3 [0,1,2]`,
`hydraIterate_K`).  Sources: Antihydra and BB(2,5) Hydra from sligocki's
`rust/src/validator.rs` (`test_antihydra` rules 4–6, `test_hydra`; opened in
`~/src/bb-deep-dive/sligocki-busy-beaver`); #323 and #218 from int-y1's `Size23Summary.lean`
(opened).

| Claim | Declaration | Folklore? |
|---|---|---|
| Antihydra is `A 3` (`H` from `2³`, walk `+2/−1`, counter 0) | `antihydra_iff_A3` | yes (definitional) |
| int-y1 #323 is `A 1` (`x + 2` follows `H`) | `hydra323_iff_A1` | int-y1's notes do not say so; Discord unknown (~40%) |
| BB(2,5) Hydra is `H` from `3`, walk `−1/+2` (`a = 3u − 6`) | `hydraBB25_iff` | **yes**: the substitution `(3a − 6, b)` is on the bbchallenge wiki (dyuan01, page for `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`; web search snippet, page not opened) |
| **#323 and BB(2,5) Hydra walk the same orbit `H^n(3)`**, with mirrored weights | `hydra323_hydraBB25_same_orbit` | not seen anywhere (~50% folklore, since it follows from the two rows above) |
| `A 0`, `A 4` halt (walk steps 1, 22) | `not_A0`, `not_A4` | known-answer controls |
| #218 is the `K`-orbit of 4 (`x + 3` follows `K`) | `hydra218_iff` | int-y1 likely knows (~50%) |

So "Hydra never halts" says the odd density of `H^n(3)` stays above about 1/3 (`E_n ≤ 2 O_n`).
"#323 never halts" says the odd density of the *same* sequence stays below about 2/3
(`O_n ≤ 2E_n + 2`).  The two are the two halves of one equidistribution statement about one
orbit.  Neither implies the other (paper, 95%: different inequalities).

**Bigfoot vs #218 (computed, negative).**  Both have slope 4/3, but Bigfoot's engine is not `K`
in disguise at the block level.  LegionMammal978's block map has offset spread
`max − min of s(r) − 256r/81 = 196/81`, while every 4-fold composition of `⌊4u/3⌋` and `⌈4u/3⌉`
has spread `350/81`.  An affine conjugacy `u = λβ + t` multiplies spread by `|λ|`, and it needs
`λ ∈ ℤ` to preserve `ℤ`; `350/196 = 25/14 ∉ ℤ`, so no affine conjugacy exists (paper, 90%).  A
brute-force search (`λ ∈ {±1, ±2, ±4, ±1/2}`, `|t| < 300`, all 16 roundings) found none either.
In `X = 4b + 3c` the one-step offset `X' − 4X/3` depends only on `(b mod 2, X mod 3)`: it is
`3, −1/3, 7/3` at odd `b` and `2, −10/3, 22/3` at even `b` (computed, 4000 steps).  Bigfoot is two
alternating `×4/3` engines, each applied twice in a row, and neither is a rounding of `4X/3`
(the offset spread exceeds 1).

## 5. The Maze gate on `KPosCascade` (Lean)

**What `KPosCascade` says, exactly** (`lean/Collatz/Bigfoot/V6Bridge.lean`).  Under
`φ(a, b, c) = (k := a, a := 2b − 1, b := 2c + 1, P1)`, one Ligocki step from `s` is one V6 segment
from `φ s` to `φ(step s)`: `⌊b/6⌋` B/S pairs (`cascade`), then a tail of 2–3 rules chosen by
`b mod 6` (`seg0` … `seg5`, `segment`).  The only decrement firings, `(P1, a = 9)` (B-coll) and
`(P1, a = 3)` (D-W), occur exactly in the segments with `b ≡ 5` and `b ≡ 2 (mod 6)`, with `k = a`
(`segment_fire`, `SegFire`).  Hence

* **`kPosCascade_iff_margin2`**: `V6.KPosCascade ↔ Margin2`, where
  `Margin2 := ∀ n s, Dyn.orbit n = some s → s.b % 6 ∈ {2, 5} → 2 ≤ s.a`.
* `margin2_nonhalt`: `Margin2 → ∀ n, Dyn.orbit n ≠ none`.

Correction to a docstring: `V6KPos.lean` describes `KPosCascade` as "equivalent to Ligocki's
InvariantA, i.e. to the holdout".  As statements they are not equivalent.  Non-halting is
`b ≡ 2 → a ≥ 1`, and `KPosCascade` asks for margin 2 at `b ≡ 2` *and* at the harmless `b ≡ 5`
steps, where V6's B-coll passes through `k − 1` before Q-kpp restores it.  So the repo's crux is a
strictly stronger-looking form of the holdout (one direction is proved), of the same kind.
Empirically both hold: min `a` at `b ≡ 2, 5` over `10⁵` steps is `3` (computed).

**Gate verdict: costume** (`lean/Collatz/Bigfoot/Gate.lean`).  The increment of the counter is
local: `walk_local` makes it a function of `b mod 6`, i.e. of the clock phase and `b mod 3`.  The
counter itself is not: by `a_not_local`, it is not a function of `(n mod 4, b mod 3^j)` for any
`j ≤ 8`, with explicit kernel-checked collisions on the orbit.  Computed over `10⁵` steps,
essentially every key `(phase, b mod 3^j)` with `j ≤ 8` has several values of `a` (`12/12, …,
23492/25651` keys), while the increment shows zero conflicts (the control).  So `KPosCascade` is
"the partial sums of a digit-driven walk along one orbit stay ≥ 2 at the decrement residues".
That is the Antihydra-type single-orbit wall (crossreview §0: one specific orbit's residue
statistics), not a within-horizon statement.  No renewal in V6 coordinates rescues it, because
V6's `k` *is* Ligocki's `a` along the orbit (`segment`).

## What is not claimed

Nothing here bears on whether Bigfoot halts.  The block map and the clock-in-substance are prior
work (LegionMammal978).  The Hydra-to-`H` substitution is prior work (dyuan01, wiki).  The
prior-work search was a local read of `bb-deep-dive` and int-y1 plus one web search: the
bbchallenge Discord (`#bb3x3`, `#bb-fractran`) was **not** searched, and either the parity lemma
or the #323/Hydra shared orbit may be known there.

## Build

`lake build` at the repo root; the declarations are in `lean/Collatz/Bigfoot/{Clock,Gate,V6Bridge}.lean`
and `lean/Collatz/Census.lean`.
