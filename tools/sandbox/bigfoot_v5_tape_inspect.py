#!/usr/bin/env python3
"""Bigfoot TM, v5 (prototype, Path A): tape-parametric inspection.

Following notes/16, v4 surfaced the `(a, b, c)` recurrence in raw data
(N, AP bites, near-period-10 drift). To extract the closed-form
recurrence, we need to read the tape's parametric form directly at
super-cycle boundaries.

Strategy: at the end of each super-cycle (state == C, just after a
B-sweep, head one cell left of the right boundary), dump the tape in
RLE form and look for the `1^a 2 1^b 2 1^c [head] ...` shape — or
whatever the actual shape turns out to be.

This is exploratory; we make no assumption about the parametric form.
We just print the tape clearly enough that the eye can find the
shape.

Verification: equivalence-checked against v1 at every super-cycle.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bigfoot_v1_literal import Bigfoot as BigfootV1
from bigfoot_v4_dance_internals import BigfootV4


class BigfootV5(BigfootV4):
    """v4 + tape-shape introspection at super-cycle boundaries."""

    def tape_rle(self, lo=None, hi=None):
        """Run-length-encode the nonzero region of the tape.
        Returns a list of (symbol, run_length) pairs covering
        [lo, hi]. If lo/hi are None, uses the nonzero footprint
        plus a small margin so leading/trailing zeros are visible.
        """
        nonzero = [i for i, v in self.tape.items() if v != 0]
        if not nonzero:
            return []
        if lo is None:
            lo = min(nonzero) - 2
        if hi is None:
            hi = max(nonzero) + 2
        runs = []
        i = lo
        while i <= hi:
            sym = self.tape[i]
            j = i
            while j + 1 <= hi and self.tape[j + 1] == sym:
                j += 1
            runs.append((sym, j - i + 1))
            i = j + 1
        return runs

    def tape_str_around_head(self, left=40, right=10):
        """Pretty-print a window around the head with head marker."""
        cells = []
        for i in range(self.pos - left, self.pos + right + 1):
            s = str(self.tape[i])
            if i == self.pos:
                s = f"[{self.state}{s}]"
            cells.append(s)
        return " ".join(cells)


def fmt_rle(runs, head_pos=None, lo=None):
    """Format an RLE list as e.g. '0^inf 1^3 2 1^5 [head] 2 0^inf'.
    If head_pos and lo provided, mark the run containing the head."""
    out = []
    pos = lo if lo is not None else 0
    for sym, n in runs:
        token = f"{sym}^{n}" if n > 1 else f"{sym}"
        if head_pos is not None and pos <= head_pos < pos + n:
            out.append(f"[{token}]")
        else:
            out.append(token)
        pos += n
    return " ".join(out)


def verify_v5_against_v1(n_super_cycles=100):
    v1 = BigfootV1()
    v5 = BigfootV5()
    boot = v5.bootstrap_to_first_b_end()
    if boot is None:
        return False, "v5 halted in bootstrap"
    while v1.step_count < v5.micro_count:
        if not v1.step():
            break
    for i in range(n_super_cycles):
        info = v5.super_cycle_v4()
        if info is None:
            return True, f"halted at super-cycle {i+1}"
        while v1.step_count < v5.micro_count:
            if not v1.step():
                break
        v1_cells = {k: v for k, v in v1.tape.items() if v != 0}
        v5_cells = {k: v for k, v in v5.tape.items() if v != 0}
        if v1.pos != v5.pos or v1.state != v5.state or v1_cells != v5_cells:
            return False, f"mismatch after super-cycle {i+1}"
    return True, "ok"


def main():
    print("===== verify v5 == v1 over 200 super-cycles =====")
    ok, msg = verify_v5_against_v1(200)
    print(f"verification: {'PASS' if ok else 'FAIL'} -- {msg}")

    # First: print tape at end of bootstrap (before any super-cycles)
    print("\n===== tape at boundaries: bootstrap + first 30 super-cycles =====")
    bf = BigfootV5()
    bf.bootstrap_to_first_b_end()
    nonzero = [i for i, v in bf.tape.items() if v != 0]
    lo = min(nonzero) - 1 if nonzero else 0
    hi = max(nonzero) + 1 if nonzero else 0
    runs = bf.tape_rle(lo, hi)
    print(f"\nAFTER BOOTSTRAP:")
    print(f"  state={bf.state}  pos={bf.pos}  span=[{lo+1},{hi-1}]  "
          f"width={hi-lo-1}")
    print(f"  RLE: 0^inf {fmt_rle(runs, bf.pos, lo)} 0^inf")
    print(f"  head context: ...{bf.tape_str_around_head(20, 5)}...")

    for k in range(30):
        info = bf.super_cycle_v4()
        if info is None:
            print(f"\nhalted at super-cycle {k+1}")
            break
        nonzero = [i for i, v in bf.tape.items() if v != 0]
        lo = min(nonzero) - 1 if nonzero else 0
        hi = max(nonzero) + 1 if nonzero else 0
        runs = bf.tape_rle(lo, hi)
        print(f"\nCYCLE {k+1}:  state={bf.state}  pos={bf.pos}  "
              f"span=[{lo+1},{hi-1}]  N={info['N']}  "
              f"right_boundary={info['right_boundary']}")
        print(f"  RLE: 0^inf {fmt_rle(runs, bf.pos, lo)} 0^inf")


if __name__ == "__main__":
    main()
