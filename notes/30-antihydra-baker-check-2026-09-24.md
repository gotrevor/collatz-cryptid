# 30 - Is the Antihydra odd-count bound a Baker problem?  Verdict: NO opening for us 🌀❌

*Ren, 2026-09-24.  Answers option 2 / open question 1 of `notes/29`.  Confidence ~85%.*

## The question

In #bb6 on 2026-09-05, planet246 wrote "|odd| ≥ O(log k) is known" and "|odd| ≥ C·log k·log log k
I think would still be novel", and mxdys added "|even| ≤ 1.01^|odd| is already open".
(Here k is the step count of H(n) = n + ⌊n/2⌋ from n = 8; halting iff odd count ever exceeds
2 × even count.)  The hope in `notes/29` was that these are |2^a − 3^b| questions, where
collatz-moonshot's linear-forms-in-logs machinery (Front A, Simons-de Weger / Rhin-lite) could bite.

## Answer: Baker-shaped, yes - but both relevant tools are already run to their ceiling

The negative inventory is Marcelo Fornet's `github.com/mfornet/antihydra-autoresearch`
(local clone `~/src/reservoir/mfornet/antihydra-autoresearch`, HEAD `5962e62` 2026-09-14;
~300 notes, 43 Lean modules).  It was posted to #bb6 on 2026-09-14/15, *after* planet246's remark.

1. **Two-term Baker is done and provably capped.**  `notes/runs.md` RL1-RL3: a parity run is a
   2-adic valuation, a run starting at step K has length ≤ log₂ a_K ≈ 0.585·K, which gives the
   elementary Θ(log k) (this is planet246's "known" bound).  `notes/run-rigidity.md` RR1-RR4: the
   junction between consecutive runs is an exact equation 3^v·u − 2^w·m = 1, and Matveev/Baker
   forbids two consecutive near-cap runs.  That buys a **log log k** second-order term and nothing
   more.  RR5 proves the ceiling: alternation + caps + any bounded-window linear-forms bound is
   *satisfiable* with odd count Θ(log k), so no such argument beats the leading order.
   (Ren derived the same pairwise Yu/Matveev argument independently on 2026-09-24 before
   finding RR1 - the same result, not a new one.)
2. **Multi-term (subspace theorem) is done too, with no rate.**  `notes/sparse-sunit-digit-growth.md`
   ES3 (2026-09-06): both parity counts satisfy count / log N → ∞, unconditionally, via
   Evertse 1984 (sums of S-units).  The constants are **ineffective**, so there is no named rate.
3. **The remaining gap is a famous open problem, not a formalization target.**
   `notes/sunit-effectivity-frontier.md` QE3 names exactly what is missing: an explicit bound F(r)
   on how Evertse's constant grows with the number of terms r.  Even a double-exponential F(r)
   would give a rate like log k·(log log k)^{1/α}, i.e. roughly planet246's "novel" target.  That
   is an effective quantitative subspace theorem with explicit dimension dependence - open in
   Diophantine approximation generally.  QE1-QE2 check the best current sources (Evertse-Ferretti;
   Bajpai-Bennett's effective 5-term theorem) and show why they don't reach it.

## Why collatz-moonshot's machinery doesn't transfer

Front A's theorem (`acyclicParadoxical_length_lt_of_oddRunCount`) *does* have explicit dependence
on the run count b, which is superficially the missing F(r).  But it gets that because the
paradoxical condition bounds the starting value by the word itself (x ≤ N/D), making the problem
an S-unit equation with small coefficients.  An Antihydra segment starts at an arbitrary
x ≈ 1.5^K; that huge, non-S-unit endpoint is exactly the obstruction QE2 isolates ("the necessary
endpoint coefficient is exponentially too large").  So the transfer fails at the known wall.
*(~75% on this sub-claim: argued on paper, not tested.)*

## What this means for the brief

- Drop option 2 of `notes/29`.  The Collatz → BB bridge via Baker is real, but it's been built
  by someone else, up to a wall that is a general open problem.
- mfornet also concludes (RR11) that halting paths need no long runs, so run-length control
  can't decide Antihydra anyway: the difficulty is parity *frequency* (Mahler 3/2 territory).
  compcraftr (#bb6, 9/15): "the main thing that needs to be solved is Mahler's 3/2 problem".
- **The live connection opportunity is the people**: Marcelo Fornet (BB(5)-in-Lean author,
  Antihydra Lean project, same AI-assisted mode as us) and Ralf Stephan (`rwst/Antihydra-Basics`).

## Probe

Skipped on purpose.  The planned numeric probe was going to test how close the orbit comes to
the run caps; RR5's numerics already did that to 10⁷ steps (no run past 24% of its cap after
k = 46).  Repeating it adds nothing to a verdict that rests on their proofs.
`golirt1/antihydra-notes` could not be cloned (GitHub asked for credentials, so it is private
or renamed); its Discord summary (9/16) lists only automaton / modulus / Mahler-equation
negatives, none of them Baker-related.
