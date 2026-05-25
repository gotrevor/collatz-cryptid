# The Busy Beaver Bridge 🦍

The 800 lb gorilla. The whole point of the Lean exercise.

## The connection in one paragraph

For each `n`, there exist `n`-state Turing machines whose halting status is
*encoded* by a Collatz-like iteration: the tape configuration corresponds
(via an explicit injection) to an integer in some 3n+1-style orbit, and
the machine halts iff that orbit reaches a fixed state. If Collatz holds,
the orbit reaches `1`, and the corresponding TM is known to never halt.

These TMs sit in the **"Probviously Infinite"** bucket on
[bbchallenge.org](https://bbchallenge.org/) - "we strongly suspect they
don't halt, but proving it requires Collatz or a near relative."

Lemma to aim for, eventually:

```lean
theorem collatz_implies_M_nonhalt
    (h : Collatz.Conjecture) : ¬ Halts M := …
```

Where `M` is a specific small TM. That's the prize.

## Phases

### Phase A (in progress) - Collatz in Lean

`lean/Collatz/Basic.lean`, `Conjecture.lean`, `Conditional.lean`.
Define `T`, state `Conjecture`, prove a few conditional corollaries.
Foundation for everything below.

### Phase B - A Turing machine model

Two options:

1. **Use mathlib's `Turing.TM0` / `TM1` / `TM2`** — already in mathlib, but
   the API is sparse and idiosyncratic. Built for proving undecidability,
   not for analysing specific machines.
2. **Roll our own minimal TM type** — a `structure` with finite states,
   tape symbols, transition function; a `step` function and `Halts` predicate.
   Probably cleaner for one specific machine.

Tentative pick: **roll our own**, scoped to "deterministic single-tape TM
over `{0, 1}`-alphabet, finite state set." This is what bbchallenge.org
machines are, so the encoding round-trips.

### Phase C - A specific Collatz-equivalent TM

The target `M` to formalise. Open questions:

- Which `M`? Candidates:
  - **Pavel Kropitz**-style small Collatz-like machines (well documented)
  - **Shawn Ligocki**'s "probviously infinite" entries
    ([sligocki.com](https://www.sligocki.com/))
  - The simplest known TM whose non-halting reduces to *plain* Collatz
    (vs. a Collatz cousin)
- Shawn is in Trevor's orbit (NE Open 2025 player); the right starting
  move is "ask Shawn what the cleanest target is" once Phase A compiles.

Reduction lemma to prove in Lean:

```lean
def encode (n : ℕ) : Tape := …
def decode (t : Tape) : Option ℕ := …

theorem M_step_eq_T (n : ℕ) :
    decode (M.step (encode n)) = some (T n)
```

(Or something close - precise statement depends on the encoding `M` uses.
For a Collatz simulator, "one phase of `M`" usually corresponds to "one
or several steps of `T`," so the equivalence is more nuanced.)

### Phase D - The conditional non-halting theorem

```lean
theorem collatz_implies_M_nonhalt
    (h : Collatz.Conjecture) : ¬ Halts M := by
  -- if M halts in k steps, then by the reduction the Collatz orbit of
  -- some n hits a "stuck" configuration. But by h, the orbit reaches 1,
  -- which corresponds to M's known cycle, contradicting halting.
  sorry
```

## What "having a look" buys us

Trevor's stated goal isn't "prove this." It's "see what the domain
looks like." Formalising `Conjecture`, defining `T`, stating the BB
reduction - even with `sorry`s - puts the actual structure on the page.
We can read it. We can show it to Shawn. We can iterate on the
*statements* before we ever have to write the proofs.

That alone is worth Phase A.

## References

- [bbchallenge.org](https://bbchallenge.org/) - BB(5) verified; BB(6)
  in progress. "Probviously Infinite" classification.
- [sligocki.com](https://www.sligocki.com/) - Shawn's blog,
  Collatz-like TM analyses.
- [Coq-verified BB(5) = 47,176,870](https://arxiv.org/abs/2406.08075)
  (mxdys et al., 2024) - the model for a community-scale formal
  verification of a BB result.
- Conway 1972 / 1987 - generalized Collatz problems are
  Turing-complete; hence undecidable in general. The 3n+1 case is
  the boundary.
