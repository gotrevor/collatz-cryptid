# Handoff: T2, rounding-choice foils for Antihydra (2026-10-15)

**Status at checkpoint (2026-10-15):** run stopped by the treadmill after `box done --green`.
Branch `wip/t2-antihydra-gate`, HEAD before this checkpoint `142b185`.  `lake build` green
(8770 jobs).  T2 targets 1-4 done; nothing in flight; no Aristotle job submitted.

Branch `wip/t2-antihydra-gate`.  Kickoff: `KICKOFF-2026-10-15-t2-antihydra-gate.md`.
Write-up: `notes/33-antihydra-foils-2026-10-15.md` (claims tagged Lean / source / paper).
Lean: `lean/Collatz/Antihydra/Foils.lean`, in the default build via `Collatz.Antihydra`; no
`sorry`, no axioms beyond `propext, Classical.choice, Quot.sound`, no `native_decide`.

## Targets

1. Family defined: `step`, `orbit`, `Halts`, `blk`, `member L σ`; Antihydra = `member_floor`;
   faithfulness anchor `halts_floor_iff` (↔ mfornet's `AntihydraHalts`) + `trace_check`.  DONE.
2. `exists_halting_member` (any `L ≥ 1`, agreeing with Antihydra below any block `K`), via
   `realize` + `halting_dense`.  Non-halting: `F_one_both` (L = 1), conditional
   `nonhalting_member_of_survives` for general `L`; unconditional general `L` is open and
   recorded as `def AllNonhaltingMember` (needs a two-orbit survival statement).  DONE.
3. Classification: notes/33 §2.  Headline: the crossreview's guess "every mfornet result holds
   for every member" is wrong; all `E`-lower-bounds / odd-run caps / repeat bounds are
   floor-exact (false for the odd-tail member); the blind results are `O`-lower-bounds
   (RL1-even, WR4, ES3-O), which point toward halting.  mfornet already has the F_1 chain
   ("fair stochastic rounding") and WR4; the foil conclusions are new.  DONE.
4. Ceiling: `evenCount_ceiling_lower` + `evenCount_ceiling_sharp`: the best `E_k` lower bound
   from members agreeing below block `K` is Antihydra's own `E` frozen at `horizon L K`.
   Gate: `rounding_blind_cannot_decide`.  DONE.

## Open / next (exact next steps, if T2 is resumed)
- First: Discord prior-work check for "rounding-choice foil / halting member" (host session).
- Then, optionally, `AllNonhaltingMember` for fixed small `L` via
  `nonhalting_member_of_survives` with `K = 2` (finite checks; `L ≤ 2` is immediate since the
  start `8 ≥ 4L`).
- `AllNonhaltingMember` (open def).  Small fixed `L` would be finite checks; not worth much.
- An effective blind `O_k ≥ c log k` in Lean from `even_run_dvd` (mfornet ED2's adaptation) —
  optional; it points toward halting, so it is a control, not progress on Antihydra.
- Discord prior-work check for the foil observation (needs a host session).
- (G) (`GlobalDigitBound`) is the route that passes the gate; not studied.

## Run scope
This run was a bounded kickoff (T2 only).  `box done` was signalled; the repo-wide gate declines
because 9 pre-existing sorries remain outside T2 (Tao, Korec, Bigfoot sim/V6KPos, etc.).  They are
not in scope for this kickoff.  Relaunch with `--done-when 'sorry-free:lean/Collatz/Antihydra'` (already met)
if the host should stop on T2's target.
