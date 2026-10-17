# A Goodstein Turing machine

`halt_4.json` is a 51-state, 16-symbol Turing machine that, started on a blank tape, computes the
Goodstein sequence of 4 and halts when it reaches 0.  Goodstein's theorem says it halts.  The
sequence from 4 is commonly cited as reaching 0 after `3·2^402653211 − 2` steps, and every
Goodstein step costs the machine many tape steps.  `halt_16.json` (56 states) starts from 16.
`build_halt.py N out.json` builds the machine for any seed `N`.  Only the initial tape, one state
per written cell, depends on `N`.  `halt_4_table.txt` is the transition table in readable form.

## How it computes

The tape holds `bb…b [ ] P d…d P d…d …`.  The `b`s are the current base in unary, and the work area is
the hereditary base-`b` representation of the current value as a rooted tree.  A digit `k` is
written as `k` sibling copies, in preorder, each node `P` followed by its depth in unary `d`s.
Changing the base leaves the tree unchanged, so a Goodstein step is `b += 1`, then subtract 1 in
hereditary base `b`:

    repeat: delete the last node L;
            if L was at depth 1: done;
            X := the nearest node left of L with smaller depth (L's parent);
            append b − 1 copies of the block from X to the end of the tape.

This is the identity `b^E − 1 = (b−1)·b^{E−1} + (b^{E−1} − 1)` applied along the rightmost branch.
It is also the Kirby–Paris hydra with `b − 1` copies.  Every operation happens at the right end of
the tape, so the machine needs no recursion stack.  The machine halts when the work area is empty.

## Checks (computed)

`test_halt.py` simulates a machine and compares every Goodstein step with an independent
big-integer Goodstein computation (`bump` = hereditary base change on integers).

- Seeds 1, 2, 3 halt after exactly 1, 3, 5 Goodstein steps (23, 171, 285 machine steps).
- Seed 4: the first 1533 Goodstein steps match the reference (20M machine steps, value 7 digits).

`test_fast.py` compares the tape tree, node for node, with a symbolic hereditary-base reference
(a number is a descending tuple of exponent trees), so it needs no big integers and big seeds stay
cheap.  It agrees with `test_halt.py` on seeds 1-4.  It also reports a mismatch when one transition
is corrupted.

- Seed 4: 6141 Goodstein steps match (300M machine steps, about 80 s).
- Seeds 16 and 100 (`build_halt.py`, 56 and 89 states): 1533 Goodstein steps match in 20M
  machine steps.

In the sequence from 4, the step into base `3·2^k` (12, 24, …, 1536, 3072, 6144, …) is where the
tail of the tree runs out.  There a block of about `b` nodes is copied `b − 1` times (computed
symbolically up to base 20000).  The machine spends most of its time in those steps, so a fixed
budget tends to stop just before one.  Seeds 4, 16 and 100 all stop at base 1535 under 20M steps
because their lowest levels go through the same doubling.

The table's other `---` entries are (state, symbol) pairs the construction never reads; the only
halt the machine reaches is `STEP_DONE_CHECK2` reading `]`.  That claim is argued from the
construction and observed in these runs; it is not proved.

## Proof of halting: status

1. The tree process terminates for every finite tree: this is the hydra theorem, by ordinal (or
   multiset) descent.  For the Goodstein reading, it is Goodstein's theorem.
2. The machine simulates the tree process step for step.  Tested above, not proved.

A Lean proof of (2) plus (1) would make the halting a theorem.  `beeping.json` is a related
69-state machine that runs every seed tree in turn and passes through state `BEEP` after each.
"It beeps infinitely often" implies Goodstein's theorem for every `n`, so PA cannot prove it.
