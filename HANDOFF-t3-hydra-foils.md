# Handoff: T3, rounding-choice foils for the whole Hydra schema (2026-10-17)

**Checkpoint (2026-10-17, lap 2):** branch `wip/t3-hydra-foils`.  `lake build` green (8785
jobs).  Targets 1-4 DONE, and the stretch's Bigfoot half is DONE: Bigfoot drains at defect 1
(`bigfoot_halting_member_one`, lifted certificate on `X mod 1944`) and at defect 2
(`bigfoot_halting_member_two`, `X mod 72`), via the new general-period lifted gate
`Sys.halting_dense_of_modCertN`; module `lean/Collatz/HydraFoils/BigfootLift.lean`.  Defect 0 is
the cryptid, so the Bigfoot ladder `14 → 13 → 7 → 2 → 1` is closed in the `X` coordinate.
Remaining stretch item (optional): the clocked block map (`step4_block`, slope `256/81`) as the
coordinate; since `d = 1` is already reached in `X`, its interest is only a different family.
Build tip: after editing `HydraFoils.lean`, rebuild the Cert218 chunk modules one at a time
(parallel rebuild hits the box's "too many open files"; reference corpus
`lean-box-fd-exhaustion-is-mmap-not-nofile.md`).

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
4. Sharpness: #218's window `d_min = 2` is NOT sharp: `Cert218.hydra218_halting_dense_one`
   (halting members dense in `F_{L,1}`), via the lifted gate `Sys.halting_dense_of_modCert` and a
   `3^10`-state potential checked by `decide +kernel` (`Cert218Data`, `Cert218ChunkA/B/C`).  DONE.

5. Stretch, Bigfoot lifted: `bigfoot_halting_member_two` (`d = 2`), `bigfoot_halting_member_one`
   (`d = 1`), notes/35 rows 18-21 and §3.  DONE.

## Open / next
- Stretch: clocked block map coordinate (`Dyn.step4_block`).  Optional.
- Lean statement of the lifted-game values (row 17 of notes/35) is not recorded; only the
  certificate is.
- Prior-work search (host session, no egress here).
