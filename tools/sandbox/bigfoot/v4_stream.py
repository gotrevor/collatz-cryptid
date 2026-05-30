#!/usr/bin/env python3
"""Bigfoot TM, v6: a stream of super-cycles.

Same machine, same hypothesis as v4/v5. The rewrite turns three things
inside-out:

  1. Halt is a Python exception, not a poison value.
     Every macro_step can kill the machine. v4/v5 thread that as
     `if not alive: return None/halt` through every layer. v6 raises
     Halt inside the one-liner that wraps macro_step, so dance_step
     and super_cycle bodies read top-to-bottom with no branches for
     "did it die yet."

  2. A super-cycle is a *thing*, not a dict.
     SuperCycle(bounces, drop, b_sweep_micros, right_boundary). N and
     sum_bites and max_bites are derived properties, not fields, so
     they can't drift out of sync.

  3. The simulator is a generator.
     bf.super_cycles() yields SuperCycle objects until the machine
     halts. The caller takes as many as it wants with islice(); the
     bootstrap happens implicitly on the first yield.

Hypothesis (unchanged from v4):

   dance = (C_step, A_skim) repeated N+1 times
         = N "bounces" (A_skim ends in C) + 1 "drop" (A_skim ends in B)

Each (C_step, A_skim) pair "bites" k >= 0 ones before terminating;
that integer k is the relevant per-pair state.
"""

import itertools
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator

# v1 and v3 live in the parent sandbox dir
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bigfoot_v1_literal import Bigfoot as BigfootV1
from bigfoot_v3_supercycle import BigfootV3


class Halt(Exception):
    """Raised when a macro step kills the machine. Caught at the stream layer."""


@dataclass(frozen=True)
class DanceStep:
    """One (C_step, A_skim) pair. bites = ones the A_skim ate before stopping."""
    kind: str   # "bounce" (A_skim landed in C) | "drop" (A_skim landed in B)
    bites: int


@dataclass(frozen=True)
class SuperCycle:
    """A dance (N bounces + 1 drop) followed by the post-dance B-sweep."""
    bounces: tuple    # bite counts of the N bounces
    drop: int         # bite count of the final drop
    b_sweep_micros: int
    right_boundary: int

    @property
    def n(self) -> int:
        return len(self.bounces)

    @property
    def all_bites(self) -> tuple:
        return self.bounces + (self.drop,)


class BigfootV6(BigfootV3):

    def _step(self) -> None:
        """One macro_step that turns death into an exception."""
        if not self.macro_step():
            raise Halt()

    def _dance_step(self) -> DanceStep:
        """Pre: state == C. Post: state == C (bounce) or B (drop)."""
        assert self.state == "C", f"_dance_step requires C, got {self.state}"
        self._step()
        assert self.state == "A", f"C should hand off to A, got {self.state}"
        before = self.micro_count
        self._step()
        # A_skim micros = 1 terminal transition + k ones eaten
        bites = self.micro_count - before - 1
        if self.state == "C":
            return DanceStep("bounce", bites)
        if self.state == "B":
            return DanceStep("drop", bites)
        assert False, f"A_skim ended in unexpected state {self.state}"

    def _super_cycle(self) -> SuperCycle:
        """One dance + the B-sweep that follows it. Raises Halt on death."""
        bounces = []
        while True:
            step = self._dance_step()
            if step.kind == "drop":
                drop = step.bites
                break
            bounces.append(step.bites)
        before = self.micro_count
        self._step()
        nonzero = [i for i, v in self.tape.items() if v != 0]
        return SuperCycle(
            bounces=tuple(bounces),
            drop=drop,
            b_sweep_micros=self.micro_count - before,
            right_boundary=max(nonzero) if nonzero else 0,
        )

    def super_cycles(self) -> Iterator[SuperCycle]:
        """Endless stream of SuperCycles. Bootstrap happens on first yield;
        iteration stops cleanly when the machine halts."""
        try:
            self._bootstrap_or_halt()
            while True:
                yield self._super_cycle()
        except Halt:
            return

    def _bootstrap_or_halt(self) -> None:
        if self.bootstrap_to_first_b_end() is None:
            raise Halt()


def _nonzero_cells(tm) -> dict:
    return {i: v for i, v in tm.tape.items() if v != 0}


def _states_match(a, b) -> bool:
    return (a.pos == b.pos
            and a.state == b.state
            and _nonzero_cells(a) == _nonzero_cells(b))


def verify_against_v1(n_super_cycles: int = 200) -> str:
    """Run v6 and v1 in lockstep; v1 catches up to v6's micro count after each
    super-cycle, then we check that pos/state/tape agree."""
    v1 = BigfootV1()
    v6 = BigfootV6()
    cycles_seen = 0
    for cycles_seen, _ in enumerate(v6.super_cycles(), 1):
        while v1.step_count < v6.micro_count and v1.step():
            pass
        if not _states_match(v1, v6):
            return f"FAIL: mismatch after super-cycle {cycles_seen}"
        if cycles_seen == n_super_cycles:
            return "PASS: ok"
    return f"PASS: halted at super-cycle {cycles_seen + 1}"


def describe(cycles: list) -> None:
    print("===== first 30 super-cycles, dance breakdown =====")
    for i, c in enumerate(cycles[:30], 1):
        print(f"  cycle {i:3d}:  N={c.n:3d}  b_sweep={c.b_sweep_micros:3d}  "
              f"sum_bites={sum(c.all_bites):3d}  bites={list(c.all_bites)}")

    print("\n===== integer sequences (first 50) =====")
    sequences = {
        "N (bounce count)":        [c.n for c in cycles],
        "drop bites":              [c.drop for c in cycles],
        "total bites":             [sum(c.all_bites) for c in cycles],
        "max single-bounce bites": [max(c.all_bites) for c in cycles],
    }
    for label, seq in sequences.items():
        print(f"\n{label}:\n  {', '.join(str(x) for x in seq[:50])}")

    flat = [b for c in cycles for b in c.all_bites]
    h = Counter(flat)
    print(f"\nbite-count histogram across all dance steps ({len(flat)} total):")
    for k in sorted(h)[:20]:
        print(f"    bites={k:3d}: {h[k]} ({100*h[k]/len(flat):.1f}%)")

    print("\nfirst few bite vectors:")
    for i, c in enumerate(cycles[:10], 1):
        print(f"  cycle {i}: {list(c.all_bites)}")


def main():
    print("===== verify v6 == v1 over 200 super-cycles =====")
    print(f"verification: {verify_against_v1(200)}")

    bf = BigfootV6()
    cycles = list(itertools.islice(bf.super_cycles(), 300))
    print(f"\nsimulated {len(cycles)} super-cycles "
          f"({bf.macro_count} macros / {bf.micro_count} micros)")
    describe(cycles)


if __name__ == "__main__":
    main()
