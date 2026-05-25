#!/usr/bin/env python3
"""Bigfoot TM, v1: dead-simple literal translation.

bbchallenge id 829. Transition table:

         0      1      2
    A | 1RB    2RA    1LC
    B | 2LC    1RB    2RB
    C | ---    2LA    1LA

Cell `XdY` = "write symbol X, move direction d, go to state Y".
State C on symbol 0 = HALT (the `---`).

Start: blank tape (all 0s), head at position 0, state A.

This is the most literal possible simulator. One step per call. No
optimization. No "macro" tricks. The point is to look at the
unmodified rule set and then -- in v2, v3, ... -- progressively
rewrite it to surface its structure WITHOUT changing what it computes.
"""

from collections import defaultdict


# Transition table: (state, symbol_read) -> (new_state, symbol_write, dx)
# dx = +1 for right, -1 for left. None means halt.
DELTA = {
    ("A", 0): ("B", 1, +1),  # 1RB
    ("A", 1): ("A", 2, +1),  # 2RA
    ("A", 2): ("C", 1, -1),  # 1LC
    ("B", 0): ("C", 2, -1),  # 2LC
    ("B", 1): ("B", 1, +1),  # 1RB   <- B on 1 just keeps going right
    ("B", 2): ("B", 2, +1),  # 2RB   <- B on 2 also just keeps going right
    ("C", 0): None,          # ---   HALT
    ("C", 1): ("A", 2, -1),  # 2LA
    ("C", 2): ("A", 1, -1),  # 1LA
}


class Bigfoot:
    def __init__(self):
        self.tape = defaultdict(int)   # tape[i] = symbol at position i (default 0)
        self.pos = 0                    # head position
        self.state = "A"                # current state
        self.step_count = 0             # how many micro-steps taken

    def step(self):
        """One TM micro-step. Returns False iff we halted."""
        sym = self.tape[self.pos]
        rule = DELTA[(self.state, sym)]
        if rule is None:
            return False
        new_state, write, dx = rule
        self.tape[self.pos] = write
        self.pos += dx
        self.state = new_state
        self.step_count += 1
        return True

    def run(self, max_steps):
        """Step until halt or max_steps reached. Returns 'halt' or 'limit'."""
        for _ in range(max_steps):
            if not self.step():
                return "halt"
        return "limit"

    def tape_view(self, width=30):
        """Pretty-print a window around the head."""
        lo = self.pos - width
        hi = self.pos + width
        cells = []
        for i in range(lo, hi + 1):
            s = str(self.tape[i])
            if i == self.pos:
                s = f"[{self.state}{s}]"  # mark head with state+sym
            cells.append(s)
        return " ".join(cells)


def main():
    bf = Bigfoot()
    print(f"Initial:")
    print(f"  step={bf.step_count}  pos={bf.pos}  state={bf.state}")
    print(f"  tape: {bf.tape_view(width=10)}")

    print(f"\nFirst 20 micro-steps:")
    for _ in range(20):
        bf.step()
        print(f"  step={bf.step_count:3d}  pos={bf.pos:+3d}  state={bf.state}  "
              f"tape: {bf.tape_view(width=10)}")

    # Run to a moderate depth and report
    result = bf.run(10_000)
    print(f"\nAfter 10,000 more micro-steps:")
    print(f"  step={bf.step_count}  pos={bf.pos}  state={bf.state}  result={result}")
    # Tape footprint
    used = [i for i, v in bf.tape.items() if v != 0]
    if used:
        lo, hi = min(used), max(used)
        print(f"  nonzero tape cells span: [{lo}, {hi}]  ({hi - lo + 1} cells wide)")
    else:
        print(f"  tape is all zeros")


if __name__ == "__main__":
    main()
