# Handoff: T3, rounding-choice foils for the whole Hydra schema (2026-10-17)

Branch `wip/t3-hydra-foils`.  Kickoff: `KICKOFF-2026-10-17-t3-hydra-foils.md`.
Write-up: `notes/35-hydra-foils-2026-10-17.md` (claims tagged Lean / computed / paper).
Lean: `lean/Collatz/HydraFoils.lean`, in the default build; no `sorry`, axioms
`propext, Classical.choice, Quot.sound`, no `native_decide`.  Scripts: `sim/hydra_foils/`.

## Targets

1. Generic family `Sys`, `Sys.step` (defect `d`, choice `τ : ℤ → Fin (d+1)`), block members
   `member q L σ`; anchors `Sys.step_zero` (= `hydraIterate`), `Sys.hydra_iff`.  DONE.
2. `q = 2` gate: `Sys.window_two` + `Sys.halting_dense_of_window`; instances
   `antihydra_halting_dense`, `hydra323_halting_dense`, `hydraBB25_halting_dense`; T2 agreement
   `antihydra_t2_halts_iff`, `t2_member_emb`, `antihydra_t2_recovered`.  DONE.
3. Window gate for every `p > q ≥ 1` (`Sys.halting_dense_of_window`, from the general
   `Sys.halting_dense_of_drain`); #218 `d = 2` (`hydra218_window`, `hydra218_halting_dense`);
   Bigfoot: window 14, reachable window 13, drift certificate 7 (`bigfoot_window`,
   `bigfoot_resWindow`, `bigfoot_drift`, `bigfoot_halting_member`).  DONE.
4. Sharpness: #218's `d_min = 2` is NOT sharp [computed]: lifted game on `u mod 3^10` has value
   −0.074 at `d = 1`; energy certificate `m = 14`, `φ ≤ 135`, trap = all states.  Lean: IN
   PROGRESS (see PENDING_WORK.md).
