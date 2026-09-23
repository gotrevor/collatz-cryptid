# 28 - bbchallenge Discord catch-up, 2026-05-26 → 2026-09-23 📥

Source: `data/discord/2026-09-23/` (gitignored; `discord-export`, 7 channels + 20 forum threads).
Digested by two reading agents + spot checks.  Usernames and dates are from the export.

## BB(3,3) - nothing moved on our holdouts
- No holdout closed; no posted progress on Bigfoot, 397, 531, 153/758; no 153≡758 or 531≡532 proofs.
- **"Kevin" = #758** (realtheepshe list, yves30. "Ok for kevin", 9/17).  Same behaviour class as 153.
- maksandchael simulated #758 to A(1, 10^11+16) (5/27-6/3); ~42M needed to "surpass the big wall".
  legionmammal978 (6/2) limiting odds: 4/9 double-(b)/(c), 2/9 (h), 1/3 (j).
- yves30. 9/16: S(3,3) "is pending on the nonhalting of Fat and Wily Coyote and cryptid Bigfoot".
- sligocki 9/16 wants the #758 wiki page rewritten: it "doesn't make it at all clear how confident
  we are in the runtime bound or even what that bound is".

## BB(6) - LLMs are closing holdouts fast
- Rocq holdouts 1104 (6/5) → 999 (8/31) → **855 / 1802 by TM (9/16)**.  mxdys 9/21 on the latest
  batch (chaotic-fractal type 1, shift-overflow counters, 10 equivalence pairs): **"all above are
  done by LLM."**  Pattern: LLM writes the informal proof, LLM translates to Rocq, Rocq checks.
- 19 cryptids on the wiki (sligocki 8/30).  New BMO problems (mxdys 8/1): **BMO9**
  `1RB1LA_1RC0RD_1LA---_1RE1RD_1LF0LA_---0LE` (racheline: "very much solvable"; aparker's sketch
  broken by obafgkm) and **BMO10** `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`.
- **Antihydra** (9/5): planet246 "|odd| >= O(log k) is known", "|odd| >= C·logk·loglogk I think
  would still be novel"; mxdys "|even| <= 1.01^|odd| is already open".  Notes repos:
  mfornet/antihydra-autoresearch, golirt1/antihydra-notes.  cosmo.st 9/18: emailed sketch of an
  Antihydra irregularity proof; sligocki "would love to see this written up".
- sligocki 6/10: "no direct reductions between Collatz-like problems AFAIK".
- DeepMind/Gemini pipeline (dsantosmarco 7/22): rules for 3 holdouts in Lean, none decided.

## Lean in the BB world
- **BB(5) fully in Lean**: mnaeraxr = Marcelo Fornet, `github.com/mfornet/busybeaver`.  BB(4,2)
  6/19, Skelet #17 7/16, Skelet #1 7/25.  Skelet #1: ~36 h on 12 cores in the kernel, 28 min with
  native_decide; cosmo.st says Rocq does it in 10-20 min on one core and calls native_decide
  "buggy and full of proof of false".  ⚠️ This community rejects native_decide.
- q64 8/21: "I'm curious if LLMs trying to grind BB(6) individual proofs might be more effective in
  lean vs. rocq" - **no reply in the export**.
- int_y1, #bb-fractran: Opus 4.8 proved 602/694 BBf(23) holdouts in Lean
  (`github.com/int-y1/proofs/tree/master/BBfLean`); 21 → **13 sorrys**, 12 stated as `Hydra`
  statements (e.g. `hydra17 : Hydra 5 2 [2, 0] [-1, 2] (1, 0)` ≡ Fenrir), #601 a 2D
  piecewise-affine map.  Detail `CLAUDE_SZ23_13.md`, standalone `sz23_sorry_13.lean` (8/5).
  int_y1 also wants an **ndpc certificate checker**.
- Skepticism of unchecked AI Lean: FC PR #4586 (BMO#8 "solved", didn't compile, closed 7/23);
  Aristotle pigeonhole "equivalence" dismissed (9/22).  sligocki 8/28: "AI assisted is fine".
- sligocki 9/14 on formalizing TM (ir)regularity, which "nobody has formalized ... in any proof
  system": "Could be a fun challenge if anyone is looking for a Rocq/Lean challenge :)".

## Other
- bb2x5: dyuan01 9/15 invites a formal proof for `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---`.
  robincodes/notxxdog rewriting problem ≡ `1RB3LA1RA4LA2RA_2LA---1LA0RA3RB` (peacemaker2 6/21),
  wanted: "a more direct, human-readable proof".
- zts439 6/25: linear-recurrence identities shared by Fenrir, Hydra and reduced Collatz; asks for
  nontrivial K with K(F(x)) = c·K(x).
- racheline 7/17: Hydra 2-adic sum S_n = 3n (telescoping).

## Where our work fits (Ren's ranking, 2026-09-23)
1. **BMO9 in Lean** - direct sequel to our BMO3/4; called "very much solvable"; a named machine
   with a kernel-checked proof is exactly what stands out against the AI noise.  (Unchecked:
   whether BMO9 is in formal-conjectures yet.)
2. **Antihydra partial bounds** - "|odd| ≥ C·log k·log log k" / "|even| ≤ 1.01^|odd|" read like
   |2^a − 3^b| questions, the linear-forms-in-logs territory of collatz-moonshot's Front A
   (Simons-de Weger / Rhin-lite).  Inference, not checked: ~40% it is really Baker-shaped.
3. **int_y1's 13 Hydra sorrys** - Lean-native generalized-Collatz statements; the equivalences
   between them fit the Bigfoot `Classification.lean` style, and answer sligocki's "no direct
   reductions" remark.
4. Answer q64 with evidence (our BB33_494 Coq→Lean port; kernel-speed caveat above).
