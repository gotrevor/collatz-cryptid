#!/usr/bin/env -S uv run python3
"""Parametric super-cycle: integer arithmetic on (a, b, X) only.

If this stays in lockstep with the cell-by-cell simulator
(parametric_table.BigfootParametric), the parametric law IS the
Bigfoot recurrence -- no tape needed. We can't prove the law
rigorously here, but matching dynamics for many cycles is strong
informal evidence.

Coverage right now: X=1 to X=1 transitions, dispatched by parity of b.
  b even -> Delta=(-3, +5), N = 3(b+2)/2
  b odd  -> Delta=(-9, +11), N = 3(b+7)/2
The X=2 step and the carries (where a would go negative) are flagged
as TODO -- they're the next things to deduce.
"""

import sys
from pathlib import Path

# parametric_table is a sibling in this directory; v5_tape_inspect is up one.
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from parametric_table import BigfootParametric


class ParametricSim:
    """Bigfoot's (a, b, X) state, advanced by integer arithmetic."""

    def __init__(self, a: int, b: int, X: int):
        self.a, self.b, self.X = a, b, X

    def state(self):
        return (self.a, self.b, self.X)

    def step(self):
        """Apply one super-cycle. Returns (N, kind) or raises if we hit a
        case we haven't deduced yet."""
        if self.X == 1 and self.b % 2 == 0:
            N = 3 * (self.b + 2) // 2
            if self.a < 3:
                raise CarryNeeded(f"(-3,+5) would underflow a (a={self.a})")
            self.a -= 3
            self.b += 5
            return N, "(-3,+5)"
        if self.X == 1 and self.b % 2 == 1:
            N = 3 * (self.b + 7) // 2
            if self.a < 9:
                raise CarryNeeded(f"(-9,+11) would underflow a (a={self.a})")
            self.a -= 9
            self.b += 11
            return N, "(-9,+11)"
        if self.X == 2:
            raise NotDeduced("X=2 step not yet encoded")
        raise NotDeduced(f"unhandled state (a,b,X)=({self.a},{self.b},{self.X})")


class CarryNeeded(Exception):
    """The parametric law would underflow a -- a carry happens instead."""


class NotDeduced(Exception):
    """We haven't worked out this case yet."""


def main():
    # Cell simulator -- ground truth.
    cell = BigfootParametric()
    cell.bootstrap_to_first_b_end()

    # Advance past the bootstrap phase to a stable-fossil state with X=1.
    # The fossil settles at L=6 around cycle 10; we want to be inside an
    # epoch (not at a carry boundary), so we advance to cycle 18.
    SEED_CYCLE = 18
    for _ in range(SEED_CYCLE):
        info = cell.super_cycle_v4()
    p = cell.parse_parametric()
    if p["X"] != 1:
        raise RuntimeError(f"expected X=1 seed, got X={p['X']}")

    parametric = ParametricSim(p["a"], p["b"], p["X"])
    print(f"seeded both simulators at (a, b, X) = {parametric.state()}")
    print()
    print(f"{'k':>3}  {'kind':>9}  {'(a,b,X) param':>18}  {'(a,b,X) cell':>18}  "
          f"{'N param':>7}  {'N cell':>6}  match?")
    print("-" * 78)

    k = 0
    while True:
        k += 1
        try:
            N_p, kind = parametric.step()
        except CarryNeeded as e:
            print(f"{k:>3}  CARRY     param halted: {e}")
            print(f"     cell at this point: ({cell.parse_parametric()['a']},"
                  f"{cell.parse_parametric()['b']},{cell.parse_parametric()['X']})")
            break
        except NotDeduced as e:
            print(f"{k:>3}  TODO      {e}")
            break

        info = cell.super_cycle_v4()
        if info is None:
            print(f"{k:>3}  cell halted")
            break
        cp = cell.parse_parametric()
        cell_state = (cp["a"], cp["b"], cp["X"])
        match = parametric.state() == cell_state and N_p == info["N"]
        marker = "OK" if match else "MISMATCH"
        print(f"{k:>3}  {kind:>9}  {str(parametric.state()):>18}  "
              f"{str(cell_state):>18}  {N_p:>7}  {info['N']:>6}  {marker}")
        if not match:
            break


if __name__ == "__main__":
    main()
