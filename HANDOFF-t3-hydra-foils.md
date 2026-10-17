# Handoff: T3, rounding-choice foils for the whole Hydra schema (2026-10-17)

**Checkpoint (2026-10-17, lap budget reached):** branch `wip/t3-hydra-foils`, HEAD `bd5e171`
before this checkpoint commit.  `lake build` green (8784 jobs).  Targets 1-4 DONE; no uncommitted
work; no Aristotle job.  `box done` not yet signalled: only the kickoff's stretch item is open.
Next lap: either signal `box done "T3 targets 1-4 proved, notes/35 written"` or take the stretch
(Bigfoot lifted certificate below defect 7, see "Open / next").  Kernel-cost tips for large
certificates: notes/35 §4 build notes (`Nat.beq`, raw `Nat` ops, data in its own module,
`Elab.async false` in chunk modules).

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

## Open / next
- Bigfoot: lift the drift certificate to `X mod 24·3^j` (game solver `sim/hydra_foils/g.js`
  generalizes) to push its defect below 7; `d ≤ 6` has no residue-level certificate [computed].
- Lean statement of the lifted-game values (row 17 of notes/35) is not recorded; only the
  certificate is.
- Prior-work search (host session, no egress here).
