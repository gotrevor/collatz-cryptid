#!/usr/bin/env python3
"""Bigfoot TM, v2: same behavior as v1, macroscopic step granularity.

We collapse two "skim" loops in the rule table into single macro-steps:

  A right-sweep (A-eats-1s):
    A scans right while reading 1, converting each 1 to 2.
    Terminates when it sees a non-1 (either 0 or 2). Then:
      - if hit a 2: write 1, move LEFT, enter C    (the A-on-2 rule)
      - if hit a 0: write 1, move RIGHT, enter B   (the A-on-0 rule, starts B-sweep)

  B right-sweep:
    B scans right reading 1s and 2s, without modifying them.
    Terminates only when it sees a 0. Then:
      - write 2, move LEFT, enter C                (the B-on-0 rule)

C is still one step (it's not a sweep -- it always halts or immediately
hands off to A after one cell of movement).

So Bigfoot's nine micro-rules collapse to FOUR macro-operations:
  (1) A_skim_right   -- eats 1s, ends on 0 or 2
  (2) B_skim_right   -- skims 1s and 2s, ends on 0
  (3) C_step         -- one micro-step (1-or-2 swap, into A); or HALT on 0
  (4) A_on_0 / A_on_2 boundary transitions are part of (1)
  (4') B_on_0 boundary transition is part of (2)

The macro-step count is much smaller than the micro-step count, but
the TAPE and final (state, pos) match v1 exactly at every macro
boundary. Verified by the `verify_against_v1` test below.
"""

from collections import defaultdict
import sys
import os

# Import v1 for equivalence testing
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bigfoot_v1_literal import Bigfoot as BigfootV1


class BigfootV2:
    def __init__(self):
        self.tape = defaultdict(int)
        self.pos = 0
        self.state = "A"
        self.micro_count = 0   # equivalent micro-steps consumed by all macros so far
        self.macro_count = 0   # macro-steps taken

    def macro_step(self):
        """Take one macro-step. Returns False iff we halted."""
        s = self.state

        if s == "A":
            # A_skim_right: walk right turning 1s into 2s.
            p = self.pos
            count_1s = 0
            while self.tape[p] == 1:
                self.tape[p] = 2
                p += 1
                count_1s += 1
            # Now at first non-1 cell at position p.
            sym = self.tape[p]
            if sym == 0:
                # A_on_0: write 1, move right, enter B
                self.tape[p] = 1
                self.pos = p + 1
                self.state = "B"
                self.micro_count += count_1s + 1
            else:
                # sym == 2: write 1, move left, enter C
                self.tape[p] = 1
                self.pos = p - 1
                self.state = "C"
                self.micro_count += count_1s + 1
            self.macro_count += 1
            return True

        elif s == "B":
            # B_skim_right: walk right past 1s and 2s, leaving them
            # untouched, until we hit a 0.
            p = self.pos
            count = 0
            while self.tape[p] != 0:
                p += 1
                count += 1
            # Hit a 0 at position p. B_on_0: write 2, move left, enter C.
            self.tape[p] = 2
            self.pos = p - 1
            self.state = "C"
            self.micro_count += count + 1
            self.macro_count += 1
            return True

        else:  # s == "C"
            # C is NOT a sweep -- exactly one micro-step.
            sym = self.tape[self.pos]
            if sym == 0:
                return False  # HALT
            elif sym == 1:
                self.tape[self.pos] = 2
            else:  # sym == 2
                self.tape[self.pos] = 1
            self.pos -= 1
            self.state = "A"
            self.micro_count += 1
            self.macro_count += 1
            return True

    def run_macro(self, max_macro_steps):
        for _ in range(max_macro_steps):
            if not self.macro_step():
                return "halt"
        return "limit"

    def tape_view(self, width=20):
        lo = self.pos - width
        hi = self.pos + width
        cells = []
        for i in range(lo, hi + 1):
            s = str(self.tape[i])
            if i == self.pos:
                s = f"[{self.state}{s}]"
            cells.append(s)
        return " ".join(cells)


def verify_against_v1(n_macro_steps=2000):
    """Run v1 micro-step-by-micro-step alongside v2 macro-step-by-macro-step.
    After each v2 macro step, advance v1 by the same number of micro steps
    and confirm (tape, pos, state) match exactly."""
    v1 = BigfootV1()
    v2 = BigfootV2()
    for i in range(n_macro_steps):
        # Capture v2's micro-count BEFORE the macro step
        prev_micro = v2.micro_count
        alive2 = v2.macro_step()
        target_micro = v2.micro_count
        # Step v1 forward to catch up (or until it halts)
        while v1.step_count < target_micro:
            alive1 = v1.step()
            if not alive1:
                break
        # Check equivalence
        same_pos = (v1.pos == v2.pos)
        same_state = (v1.state == v2.state)
        # Compare tapes by nonzero cells
        v1_cells = {i: v for i, v in v1.tape.items() if v != 0}
        v2_cells = {i: v for i, v in v2.tape.items() if v != 0}
        same_tape = (v1_cells == v2_cells)
        if not (same_pos and same_state and same_tape):
            print(f"MISMATCH at macro step {i+1}:")
            print(f"  v1: pos={v1.pos} state={v1.state} micro_count={v1.step_count}")
            print(f"  v2: pos={v2.pos} state={v2.state} micro_count={v2.micro_count}")
            if not same_tape:
                diff_keys = set(v1_cells.keys()) ^ set(v2_cells.keys())
                diff_vals = {k for k in v1_cells.keys() & v2_cells.keys()
                             if v1_cells[k] != v2_cells[k]}
                print(f"  tape differs at positions: {sorted(diff_keys | diff_vals)}")
                print(f"  v1 tape: {sorted(v1_cells.items())[:20]}")
                print(f"  v2 tape: {sorted(v2_cells.items())[:20]}")
            return False
        if not alive2:
            print(f"Both halted at macro step {i+1}.")
            return True
    return True


def main():
    print("===== verify v2 == v1 over the first many steps =====")
    ok = verify_against_v1(n_macro_steps=5000)
    print(f"verification result: {'PASS' if ok else 'FAIL'}")

    print("\n===== v2 first 20 macro steps with annotation =====")
    bf = BigfootV2()
    print(f"initial:  pos={bf.pos:+3d}  state={bf.state}  "
          f"tape: {bf.tape_view(width=12)}")
    last_micro = 0
    for i in range(20):
        prev_state = bf.state
        bf.macro_step()
        consumed = bf.micro_count - last_micro
        last_micro = bf.micro_count
        kind = {"A": "A_skim_right", "B": "B_skim_right", "C": "C_step"}[prev_state]
        print(f"macro {i+1:3d} ({kind:13s} consumed {consumed:2d} micro):  "
              f"pos={bf.pos:+3d}  state={bf.state}  "
              f"tape: {bf.tape_view(width=12)}")

    print("\n===== speed comparison: macro vs micro =====")
    bf2 = BigfootV2()
    bf2.run_macro(10_000)
    print(f"  10,000 MACRO steps -> {bf2.micro_count:,} micro-steps "
          f"({bf2.micro_count / 10_000:.1f}x compression)")
    print(f"  final: pos={bf2.pos}  state={bf2.state}")

    bf3 = BigfootV2()
    bf3.run_macro(100_000)
    print(f"\n  100,000 MACRO steps -> {bf3.micro_count:,} micro-steps "
          f"({bf3.micro_count / 100_000:.1f}x compression)")
    print(f"  final: pos={bf3.pos}  state={bf3.state}")
    used = [i for i, v in bf3.tape.items() if v != 0]
    if used:
        print(f"  nonzero span: [{min(used)}, {max(used)}]  ({max(used)-min(used)+1} cells)")


if __name__ == "__main__":
    main()
