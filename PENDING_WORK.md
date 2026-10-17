# PENDING_WORK (t3-hydra-foils)

2026-10-17: kickoff targets 1-4 are complete; see `HANDOFF-t3-hydra-foils.md` and
`notes/35-hydra-foils-2026-10-17.md`.  Advance this lap: the T2 gate is now a theorem for the
whole `Hydra` schema (`Sys.halting_dense_of_drain`, window / residue-table / lifted forms), with
instances for all five census cryptids.  #218's window bound `d_min = 2` is not sharp:
`Cert218.hydra218_halting_dense_one` (defect 1, lifted `3^10` certificate).  Bigfoot drains at
defect 7 (`bigfoot_halting_member`).

Lap 2 (2026-10-17): stretch advanced.  Bigfoot drains at defect 1, the floor
(`bigfoot_halting_member_one`; certificate on `X mod 1944`, `m = 8`), and at defect 2
(`bigfoot_halting_member_two`; `X mod 72`).  Key observation: `32 ≡ 0 (mod 8)`, so the image mod
24 depends on `⌊X/24⌋` only mod 3, and one base-3 digit of lookahead removes most of the
adversary's power.  General-period gate `Sys.halting_dense_of_modCertN`.

Remaining (optional): clocked block map (`Dyn.step4_block`, slope `256/81`) as the coordinate.

Earlier (t1-bigfoot-clock, 2026-10-15): `KPosCascade` is proved equivalent to `Margin2`
(`V6Bridge.kPosCascade_iff_margin2`); a single-orbit walk statement, the open problem in costume.
