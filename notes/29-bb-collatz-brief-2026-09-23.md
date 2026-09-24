# 29 - Busy Beaver × Collatz: state of play and options (brief for a second opinion) 🦫🌀

*Written by Ren (Claude) for Trevor, 2026-09-23, to hand to Astra for suggestions.  Self-contained;
every claim points at a file you can open.*

## 0. The question

Trevor runs two Lean 4 projects that touch Collatz-like dynamics and wants to know **what, if
anything, the Collatz work and the bbchallenge Busy Beaver community can contribute to each other**,
and whether doing BB work in **Lean rather than Rocq** is a good bet for an LLM-heavy workflow.
His motives (in order of weight they're equal): real meaty math, connection with the formalization
community, and a career runway toward formalization-AI.  Targets should be meaty, self-contained,
and welcome upstream.

## 1. Our assets

**`~/src/collatz-cryptid`** (private GitHub `gotrevor/collatz-cryptid`, branch `init`; Lean 4.33.1 +
mathlib).  Layout and history: `README.md`, `HANDOFF.md`, `BB33-494-HANDOFF.md`, `BIGFOOT-HANDOFF.md`,
`notes/01-27`.
- **Bigfoot** (BB(3,3) cryptid): `lean/Collatz/Bigfoot/Classification.lean` proves its dynamics is a
  6-case residue-affine map on ℕ³ (Conway/Lagarias generalized-Collatz family); non-halting is
  reduced to one open lemma `InvariantA` (`InvariantSketch.lean`).  A (k,a,b) recurrence
  (`V6Rule.lean`) is proved halt-free but that is *not* TM non-halting (notes/17-18).
- **BB(3,3) #494**: busycoq `BB33_494.v` ported Coq → Lean, `no_halt` sorry-free.
- **Holdouts 397 "Fat Coyote", 531 "Wily Coyote"**: scaffolds + large empirical burns (notes/13-21);
  no clean parametric reduction exists.
- **Beaver Math Olympiad #3 and #4**: proved, axiom-clean, statements verbatim from
  google-deepmind/formal-conjectures (`lean/Collatz/BMO/`).  Unpublished: needs the repo public
  to link as `formal_proof`.
- **Erdős / Mahler 3/2 bridge** (`lean/Collatz/Erdos/`): Lagarias identity, carry machinery,
  2 is a primitive root mod 3^k, cycle-remainder rotation lemma, Baker-axiom ⇒ no small cycle.

**`~/src/collatz-moonshot`** (public, `github.com/gotrevor/collatz-moonshot`): an attack on Collatz
itself.  Front A proved, via a Simons–de Weger / "Rhin-lite" linear-forms-in-logs mechanism, that
acyclic "paradoxical" segments with ≤ b odd runs have bounded length; the uniform-in-b version
is the wall.  Strategy docs: `DIRECTION.md`, `APPROACHES.md`, `FABLE-NEXT-SESSION.md`.

## 2. What the community did, 2026-05-26 → 09-23

Full digest with quotes, dates, usernames and machine strings:
**`~/src/collatz-cryptid/notes/28-discord-catchup-2026-09-23.md`**.  Raw export (7 channels + 20
forum threads, plain text): `~/src/collatz-cryptid/data/discord/2026-09-23/` (gitignored).

Headlines:
- **BB(3,3)**: none of our holdouts moved.  S(3,3) still waits on non-halting of Bigfoot, Fat
  Coyote, Wily Coyote; the champion "Kevin" (#758) is probviously halting but unproven.
- **BB(6)**: Rocq holdouts 1104 → **855** since June, the latest batches **"all ... done by LLM"**
  (mxdys) - LLM writes the informal proof, LLM translates to Rocq, Rocq checks.  19 cryptids.
  New BMO problems **#9** and **#10** (neither is in formal-conjectures yet; checked 2026-09-23).
- **Lean**: BB(5) is now **fully proved in Lean** (Marcelo Fornet, `github.com/mfornet/busybeaver`).
  int_y1 used Opus to prove 602/694 BBf(23) FRACTRAN holdouts in Lean
  (`github.com/int-y1/proofs/tree/master/BBfLean`), leaving **13 sorrys, 12 stated as Collatz-like
  `Hydra` statements**.
- **Culture**: AI help is welcome ("AI assisted is fine", sligocki), but non-compiling or trivial AI
  Lean has been publicly shot down twice (FC PR #4586; an Aristotle pigeonhole "equivalence").

## 3. Lean vs Rocq - the evidence

- **Speed is Lean's real weakness here.**  The heaviest BB(5) certificate (Skelet #1) takes
  **~36 h on 12 cores** in Lean's kernel, vs **10-20 min on one core** in Rocq (cosmo.st).  That is
  ~432 vs ~0.25 core-hours - closer to **three** orders of magnitude than one, for this proof.  With
  `native_decide` Lean takes 28 min, but this community rejects native_decide ("buggy and full of
  proof of false").  Caveat: one data point, and the Lean encoding may be less tuned than
  busycoq's decades-refined one.
- **So the split is by proof type.**  Compute-heavy decider certificates favour Rocq.
  Structure-heavy, human-style arguments (invariants, arithmetic reductions, BMO-style number
  theory) cost little kernel time and benefit from mathlib - Lean's natural ground.
- **LLM fluency**: Ren's own estimate is ~75% that it writes Lean better than Rocq (more recent
  Lean 4 / mathlib text, most prover RL targets Lean); reading Rocq is fine (the #494 port).
  q64 asked this exact question in #rocq-proofs on 8/21 - "might LLMs grinding BB(6) be more
  effective in lean vs. rocq" - and nobody answered.

## 4. Where the two projects can help each other

**BB → Collatz**
1. *Known-answer controls*: every solved Collatz-like machine is a benchmark any Collatz mechanism
   should reproduce or explain failing on.  The moonshot has no controls outside Collatz itself.
2. *Barrier examples*: probviously-halting siblings (Kevin) play the role 3x−1 plays for Collatz -
   a method that "proves" them non-halting is broken.
3. *Certificates*: their deciders are the machine-found-certificate route, whose ceiling is compute.

**Collatz → BB**
1. **Antihydra partial bounds.**  In #bb6 (9/5): "|odd| ≥ O(log k) is known", "|odd| ≥ C·log k·
   log log k ... would still be novel" (planet246); "|even| ≤ 1.01^|odd| is already open" (mxdys).
   These look like |2^a − 3^b| questions, the linear-forms-in-logs ground of moonshot Front A.
   *Unchecked inference, ~40%.*
2. **Lean reductions between Collatz-like problems.**  sligocki (6/10): "no direct reductions
   between Collatz-like problems AFAIK".  Bigfoot's `Classification.lean` is that style.
   ❌ **Corrected 2026-09-24 (Astra):** the 12 Hydra sorrys are NOT an equivalence opening -
   int_y1 already did the reductions (92 → 12 via `Conjugacy.lean`) and reports "The 12 do not
   collapse any further", all 66 pairs statistically independent
   (`~/src/reservoir/int-y1/proofs/BBfLean/CLAUDE_SZ23_13.md`).
3. **Tao-style "almost all" results do not transfer** - a machine has one start, so density-1
   statements say nothing.

## 5. Options, ranked (Ren's view)

1. **BMO#9 non-halting in Lean** (`1RB1LA_1RC0RD_1LA---_1RE1RD_1LF0LA_---0LE`).  Direct sequel to
   BMO3/4, called "very much solvable" (racheline), not in formal-conjectures, and structural
   rather than compute-heavy, so Lean's kernel speed doesn't bite.  ~70%.
2. ~~**Antihydra partial bound**~~ - withdrawn 2026-09-24: mfornet/antihydra-autoresearch already
   ran both Baker (capped at log k + log log k) and the subspace theorem (odd/log → ∞, no rate);
   the rest is an effective-subspace-theorem open problem.  See `notes/30`.
3. ~~**int_y1's Hydra sorrys**~~ - withdrawn 2026-09-24: the reductions are done (see §4); what
   remains is Hydra-hard, one prop at a time.
4. **Formalize TM (ir)regularity** - "nobody has formalized regularity in any proof system";
   sligocki 9/14: "a fun challenge if anyone is looking for a Rocq/Lean challenge".
5. **Answer q64 with data** - our #494 port plus the speed numbers above.

Not recommended: porting BB(6) wholesale to Lean (huge, and exactly where the kernel is slowest).

## 6. Open questions for a second opinion

- Is the Antihydra |odd| lower bound genuinely a linear-forms-in-logs problem, or is the
  difficulty elsewhere (parity-sequence equidistribution, like Mahler 3/2)?
- BMO9 first, or the community-facing Hydra sorrys first, given the goal is connection as much as
  results?
- Publishing: the BMO3/4 proofs sit in a private repo.  Publish collatz-cryptid, or carve the BMO
  work into a small public repo?
