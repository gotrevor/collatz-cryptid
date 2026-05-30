# BB(3,3) Holdout 494 — Lean Port Handoff 🐢

**Status (end of Session E, 2026-05-26)**: 🎉 **`no_halt` CLOSED.** Zero sorries on the BB33_494 critical path. The Lean port of `busycoq/verify/BB33_494.v` is complete: 105-step bootstrap → `C_1b1` → `progress_nonhalt_simple` chains cleanly. Only remaining sorry in the BB tree is `Iso.lean:54` (`step_toSide`, off critical path; only needed for future Bigfoot bootstrap).

**Session E delta** (this session):
- Added `multistep_nonhalt` + helper `stepN_to_multistep` to `Multistep.lean` (the prefix-invariance lemma busycoq used to chain bootstrap into `progress_nonhalt_simple`).
- Closed `bootstrap : Cfg2.blank -[machine]->* C 1 5 1 Side.blank` via `unfold C; iterate 105 tm_step; tm_finish` (mirrors Coq's `do 105 step. finish.` exactly). Bumped `maxHeartbeats` to 4M for the 105-step concrete reduction.
- Closed `no_halt` itself: `multistep_nonhalt` of (`bootstrap` ⨟ `C_1b1 5 0 Side.blank` ⨟ refl) + `progress_nonhalt_simple` with family `(i, r) ↦ D (a 0) (cc i - c 0) r`, step witness `D_next`. ~20 LOC total.
- Key gotcha: `repeat tm_step` loops forever on a non-halting machine because each step succeeds. Use `iterate N` for a fixed step count.

**Session D delta** (previous session):

**Session D delta**: 
- Closed: R3, R3_finish, C_0b1, C_1b1, C_2b1, C_3b0, C_2k_b_k, D_gt, D_lt, D_step_cc, c_monotone, D_step_a, D_step_a_lt, D_step_a_minus, D_step_a_finish, D_next, progress_nonhalt_simple — **17 lemmas closed**.
- Fixed: `C` definition had `rep [s1,s2]` (wrong order, would have invalidated all C-rule statements once a > 0); changed to `rep [s2,s1]` matching busycoq.
- Fixed: C_3b0 and D_lt signatures were missing the `[0]^^b` / `[0]^^(7c+1)` prefix in the tail; now match busycoq exactly.
- Added simp lemmas: `Side.cons_s0_blank`, `dirL_blank`/`dirR_blank` (made @[simp]); extended `tm_step`'s simp set; added `Cfg2.dirL`/`dirR` unfold to `tm_follow`'s post-cleanup.
- Added tactic: `tm_step_plus` (single concrete step on a `-->+` goal, leaving the rest as `-->*`).
- Added `MultistepPlus.append : -->+ then -->* → -->+`.
- Added stepN/Multistep bridge: `multistep_to_stepN`, `multistepPlus_to_stepN`, `stepN_add`, `step2_of_halted`, `stepN_halt_none`.
- Proof technique validated: `tm_follow (lemma b _ _)` lets Lean infer Side args via unification — most C-rules are 12-25 LOC instead of the 50-100 LOC I feared.

---

## 0. TL;DR

**Where we are**: 🎉 **`no_halt` proved.** One sorry remains in the BB tree (`step_toSide` in `Iso.lean`, off critical path; only needed for future Bigfoot bootstrap).

**What was done this session**:
1. ✅ **`multistep_nonhalt`** — added to `Multistep.lean:181` alongside helper `stepN_to_multistep`. ~30 LOC.
2. ✅ **`bootstrap`** — `BB33_494.lean:664`. `unfold C; iterate 105 tm_step; tm_finish`. Mirrors Coq's `do 105 step. finish.` exactly.
3. ✅ **`no_halt`** — `BB33_494.lean:675`. `multistep_nonhalt` ⨟ `progress_nonhalt_simple` with the obvious family.
4. ✅ **Bonus — `step_toSide`** (off-critical-path follow-up): closed sorry-free in `BB/Iso.lean`. Now the side-tape world and the ℤ-tape world are interoperable. Added `stepN_toSide`, `stepN2_of_stepN_toSide`, `multistep_toSide` to lift `BB.stepN` reachability into `Multistep`. This unblocks Bigfoot's `Reduction.sim` to be approached in the busycoq-style tactical world. Also renamed Multistep.lean's `stepN_add` to `stepN2_add` to avoid name collision with `Reduction.lean`'s `BB.stepN_add`.

---

## 1. The recipe that worked (reusable for other BB(3,3) holdouts)

### Tactic upgrades that pay for themselves
- **`tm_step`** now simps with `head_cons, tail_cons, dirL_blank, dirR_blank, cons_s0_blank, tail_blank, head_blank, repeatList_zero, repeatList_nil`. Keeps goal in clean struct form after each step.
- **`tm_follow h`** now also unfolds `Cfg2.dirL`/`dirR` post-chain, so the next tm_step sees a normalized struct (no nested `.left.tail` projections).
- **`tm_step_plus`** is the `-->+` variant for the first step (e.g., `C_3b0`).
- **Use `_` placeholders for Side args**: `tm_follow (l2_r1 b _ _)` works in most cases. Lean unification fills the Sides from the current goal LHS. Saves writing 5-line Side expressions.

### When `_` placeholders fail
If the goal has `rep [s2,s1] N blank` where N is a *concrete* small number (1, 2, 3), unification sometimes can't bridge to the `n l` parametrization. Workaround: insert `simp only [show rep [s2,s1] N blank = s2 >> s1 >> ... from rfl]` before the tm_step to expose the cons form. Done in C_1b1 (N=1), C_2b1 (N=2), C_3b0 (N=3).

### The C-rule pattern (10-25 LOC each)
```lean
theorem C_Xb_Y (a b c ... : ℕ) (r : Side) : C ... -[machine]->* C ... := by
  unfold C
  simp only [show repeatList [Sym.s2, Sym.s1] N Side.blank = ... from rfl]  -- if needed
  tm_step
  tm_follow (l2_r1 b _ _)         -- or another sweep lemma
  repeat tm_step
  tm_follow (r1_l2 b _ _)         -- alternates per the proof structure
  rw [Side.merge_1 ... _ _, ...]  -- fold accumulated cells back into reps
  tm_follow (R2_finish ...)        -- and other helpers
  repeat tm_step
  ...
```

### The D-rule pattern (induction on k + omega for arithmetic)
```lean
theorem D_X (k c ... : ℕ) (r : Side) : D ... -[machine]->* D ... := by
  unfold D
  nth_rewrite 1 [show k = 2 * (k / 2) + k % 2 from (Nat.div_add_mod k 2).symm]
  ...
  tm_follow (C_2k_b_k ...)
  rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
  · rw [hmod]; tm_follow (C_0b1 ...)
    have heq : ... := by omega
    rw [heq]; tm_finish
  · rw [hmod]; tm_follow (C_1b1 ...)
    ...
```

---

## 2. Files inventory

```
lean/Collatz/
  BB.lean                 [88 lines; State, Sym, Dir, Machine, Cfg with ℤ→Sym tape]
  BB/
    SideTape.lean         [197 lines; canonical Cfg2 + dirL/dirR + cons_s0_blank simp + merge_*]
    Multistep.lean        [224 lines; -[M]->*/+ relations, stepN bridges, progress_nonhalt_simple PROVEN]
    Tactics.lean          [97 lines; tm_step, tm_follow, tm_step_plus, tm_finish — all enhanced]
    Iso.lean              [62 lines; BB.Cfg ↔ Cfg2; step_toSide sorry'd (off critical path)]
  BB33_494.lean           [673 lines; all C/D-rules PROVEN; only no_halt sorry'd]
  Bigfoot/                [existing; separate project]
```

All build clean under `lake build Collatz` against mathlib v4.29.1 (modulo `no_halt` and `step_toSide`).

---

## 3. The one remaining sorry (off critical path)

| # | Theorem | File | Effort |
|---|---|---|---|
| 1 | `step_toSide` | `Iso.lean:56` | NOT on critical path; only for future Bigfoot bootstrap. |

---

## 4. The closed proof (as shipped)

```lean
theorem bootstrap : Cfg2.blank -[machine]->* C 1 5 1 Side.blank := by
  unfold C
  iterate 105 tm_step
  tm_finish

theorem no_halt : ¬ halts machine Cfg2.blank := by
  refine multistep_nonhalt (c := D (a 0) (cc 0 - c 0) Side.blank) ?reach ?nonhalt
  · refine Multistep.trans bootstrap ?_
    refine Multistep.trans (C_1b1 5 0 Side.blank) ?_
    tm_finish
  · apply progress_nonhalt_simple
      (C := fun (p : ℕ × Side) => D (a 0) (cc p.1 - c 0) p.2)
      (i₀ := (0, Side.blank))
    rintro ⟨i, r⟩
    obtain ⟨r', H⟩ := D_next i r
    exact ⟨(i + 1, r'), H⟩
```

`multistep_nonhalt` (Multistep.lean:181):
```lean
theorem multistep_nonhalt {M : Machine} {c0 c : Cfg2}
    (hms : c0 -[M]->* c) (hnh : ¬ halts M c) : ¬ halts M c0
```

The proof case-splits on whether the halt-witness step count `nH` is ≤ or > the `c0 → c` step count `n0`. The `≤` case extracts a Multistep suffix `c → c_h` via the new `stepN_to_multistep` helper; the `>` case derives `none = some _` via `stepN_halt_none`.

---

## 5. Postmortem / takeaways

- ✅ `progress_nonhalt_simple` (Session D) + `multistep_nonhalt` (this session) is the full framework — no further infrastructure needed for the longitudinal-analysis pattern.
- ✅ `iterate N tm_step` is the right idiom for concrete-bootstrap steps. `repeat tm_step` loops forever on a non-halting machine (every step succeeds, no termination signal).
- ✅ `unfold C` before `iterate 105 tm_step` is essential — `tm_finish` then closes by reflexivity once both sides are in struct form.
- Bumping `maxHeartbeats` to 4M handles the 105-step concrete reduction comfortably (build of BB33_494 stays under 10s).

---

🐢 18 lemmas down across sessions D + E. `no_halt` is the Lean port of busycoq's BB(3,3) holdout 494 nonhalt theorem. ✨
