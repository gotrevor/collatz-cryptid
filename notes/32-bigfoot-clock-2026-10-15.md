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
